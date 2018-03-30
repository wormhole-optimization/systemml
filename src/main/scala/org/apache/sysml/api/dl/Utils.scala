/*
 * Licensed to the Apache Software Foundation (ASF) under one
 * or more contributor license agreements.  See the NOTICE file
 * distributed with this work for additional information
 * regarding copyright ownership.  The ASF licenses this file
 * to you under the Apache License, Version 2.0 (the
 * "License"); you may not use this file except in compliance
 * with the License.  You may obtain a copy of the License at
 *
 *   http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing,
 * software distributed under the License is distributed on an
 * "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
 * KIND, either express or implied.  See the License for the
 * specific language governing permissions and limitations
 * under the License.
 */
package org.apache.sysml.api.dl
import scala.collection.JavaConversions._
import caffe.Caffe.LayerParameter;
import caffe.Caffe.NetParameter;
import org.apache.sysml.parser.LanguageException;
import com.google.protobuf.TextFormat;
import org.apache.sysml.conf.ConfigurationManager;
import org.apache.sysml.runtime.util.LocalFileUtils;
import org.apache.hadoop.fs.FileSystem;
import org.apache.hadoop.fs.Path;
import caffe.Caffe.SolverParameter;
import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.io.InputStreamReader;
import org.apache.sysml.runtime.DMLRuntimeException
import java.io.StringReader
import java.io.BufferedReader
import com.google.protobuf.CodedInputStream
import org.apache.sysml.runtime.matrix.data.MatrixBlock
import org.apache.sysml.api.mlcontext.MLContext
import org.apache.spark.SparkContext
import org.apache.spark.api.java.JavaSparkContext

object Utils {
  // ---------------------------------------------------------------------------------------------
  // Helper methods for DML generation

  // Returns number of classes if inferred from the network
  def numClasses(net: CaffeNetwork): String =
    try {
      return "" + net.getCaffeLayer(net.getLayers().last).outputShape._1.toLong
    } catch {
      case _: Throwable => {
        Caffe2DML.LOG.warn("Cannot infer the number of classes from network definition. User needs to pass it via set(num_classes=...) method.")
        return "$num_classes" // Expect users to provide it
      }
    }
  def prettyPrintDMLScript(script: String) {
    val bufReader = new BufferedReader(new StringReader(script))
    var line      = bufReader.readLine();
    var lineNum   = 1
    while (line != null) {
      System.out.println("%03d".format(lineNum) + "|" + line)
      lineNum = lineNum + 1
      line = bufReader.readLine()
    }
  }

  // ---------------------------------------------------------------------------------------------
  def parseSolver(solverFilePath: String): CaffeSolver = parseSolver(readCaffeSolver(solverFilePath))
  def parseSolver(solver: SolverParameter): CaffeSolver = {
    val momentum = if (solver.hasMomentum) solver.getMomentum else 0.0
    val lambda   = if (solver.hasWeightDecay) solver.getWeightDecay else 0.0
    val delta    = if (solver.hasDelta) solver.getDelta else 0.0
    val regularizationType = if(solver.hasRegularizationType) solver.getRegularizationType else "L2"

    solver.getType.toLowerCase match {
      case "sgd"      => new SGD(regularizationType, lambda, momentum)
      case "adagrad"  => new AdaGrad(regularizationType, lambda, delta)
      case "nesterov" => new Nesterov(regularizationType, lambda, momentum)
      case "adam" 	  => new Adam(regularizationType, lambda, momentum, if(solver.hasMomentum2) solver.getMomentum2 else 0.0, delta)
      case _          => throw new DMLRuntimeException("The solver type is not supported: " + solver.getType + ". Try: SGD, AdaGrad or Nesterov or Adam.")
    }

  }

  // --------------------------------------------------------------
  // Caffe utility functions
  def readCaffeNet(netFilePath: String): NetParameter = {
    // Load network
    val reader: InputStreamReader     = getInputStreamReader(netFilePath);
    val builder: NetParameter.Builder = NetParameter.newBuilder();
    TextFormat.merge(reader, builder);
    return builder.build();
  }

  class CopyFloatToDoubleArray(data: java.util.List[java.lang.Float], rows: Int, cols: Int, transpose: Boolean, arr: Array[Double]) extends Thread {
    override def run(): Unit =
      if (transpose) {
        var iter = 0
        for (i <- 0 until cols) {
          for (j <- 0 until rows) {
            arr(j * cols + i) = data.get(iter).doubleValue()
            iter += 1
          }
        }
      } else {
        for (i <- 0 until data.size()) {
          arr(i) = data.get(i).doubleValue()
        }
      }
  }

  class CopyCaffeDeconvFloatToSystemMLDeconvDoubleArray(data: java.util.List[java.lang.Float], F: Int, C: Int, H: Int, W: Int, arr: Array[Double])
      extends CopyFloatToDoubleArray(data, C, F * H * W, false, arr) {
    override def run(): Unit = {
      var i = 0
      for (f <- 0 until F) {
        for (c <- 0 until C) {
          for (hw <- 0 until H * W) {
            arr(c * F * H * W + f * H * W + hw) = data.get(i).doubleValue()
            i = i + 1
          }
        }
      }
    }
  }

  def allocateDeconvolutionWeight(data: java.util.List[java.lang.Float], F: Int, C: Int, H: Int, W: Int): (MatrixBlock, CopyFloatToDoubleArray) = {
    val mb = new MatrixBlock(C, F * H * W, false)
    mb.allocateDenseBlock()
    val arr    = mb.getDenseBlockValues
    val thread = new CopyCaffeDeconvFloatToSystemMLDeconvDoubleArray(data, F, C, H, W, arr)
    thread.start
    return (mb, thread)
  }

  def allocateMatrixBlock(data: java.util.List[java.lang.Float], rows: Int, cols: Int, transpose: Boolean): (MatrixBlock, CopyFloatToDoubleArray) = {
    val mb = new MatrixBlock(rows, cols, false)
    mb.allocateDenseBlock()
    val arr    = mb.getDenseBlockValues
    val thread = new CopyFloatToDoubleArray(data, rows, cols, transpose, arr)
    thread.start
    return (mb, thread)
  }
  def validateShape(shape: Array[Int], data: java.util.List[java.lang.Float], layerName: String): Unit =
    if (shape == null)
      throw new DMLRuntimeException("Unexpected weight for layer: " + layerName)
    else if (shape.length != 2)
      throw new DMLRuntimeException("Expected shape to be of length 2:" + layerName)
    else if (shape(0) * shape(1) != data.size())
      throw new DMLRuntimeException(
        "Incorrect size of blob from caffemodel for the layer " + layerName + ". Expected of size " + shape(0) * shape(1) + ", but found " + data.size()
      )

  def saveCaffeModelFile(sc: JavaSparkContext, deployFilePath: String, caffeModelFilePath: String, outputDirectory: String, format: String): Unit =
    saveCaffeModelFile(sc.sc, deployFilePath, caffeModelFilePath, outputDirectory, format)

  def saveCaffeModelFile(sc: SparkContext, deployFilePath: String, caffeModelFilePath: String, outputDirectory: String, format: String): Unit = {
    val inputVariables = new java.util.HashMap[String, MatrixBlock]()
    readCaffeNet(new CaffeNetwork(deployFilePath), deployFilePath, caffeModelFilePath, inputVariables)
    val ml        = new MLContext(sc)
    val dmlScript = new StringBuilder
    if (inputVariables.keys.size == 0)
      throw new DMLRuntimeException("No weights found in the file " + caffeModelFilePath)
    for (input <- inputVariables.keys) {
      dmlScript.append("write(" + input + ", \"" + outputDirectory + "/" + input + ".mtx\", format=\"" + format + "\");\n")
    }
    if (Caffe2DML.LOG.isDebugEnabled())
      Caffe2DML.LOG.debug("Executing the script:" + dmlScript.toString)
    val script = org.apache.sysml.api.mlcontext.ScriptFactory.dml(dmlScript.toString()).in(inputVariables)
    ml.execute(script)
  }

  // TODO: Loading of extra weights is not supported
  def readCaffeNet(net: CaffeNetwork, netFilePath: String, weightsFilePath: String, inputVariables: java.util.HashMap[String, MatrixBlock]): NetParameter = {
    // Load network
    val reader: InputStreamReader     = getInputStreamReader(netFilePath);
    val builder: NetParameter.Builder = NetParameter.newBuilder();
    TextFormat.merge(reader, builder);
    // Load weights
    val inputStream = CodedInputStream.newInstance(new FileInputStream(weightsFilePath))
    inputStream.setSizeLimit(Integer.MAX_VALUE)
    builder.mergeFrom(inputStream)
    val net1 = builder.build();

    val asyncThreads = new java.util.ArrayList[CopyFloatToDoubleArray]()
    val v1Layers     = net1.getLayersList.map(layer => layer.getName -> layer).toMap

    for (i <- 0 until net1.getLayerList.length) {
      val layer = net1.getLayerList.get(i)
      val blobs = getBlobs(layer, v1Layers)

      if (blobs == null || blobs.size == 0) {
        // No weight or bias
        Caffe2DML.LOG.debug("The layer:" + layer.getName + " has no blobs")
      } else if (blobs.size == 2 || (blobs.size == 3 && net.getCaffeLayer(layer.getName).isInstanceOf[BatchNorm])) {
        // Both weight and bias
        val caffe2DMLLayer = net.getCaffeLayer(layer.getName)
        val transpose      = caffe2DMLLayer.isInstanceOf[InnerProduct]

        // weight
        val shape = caffe2DMLLayer.weightShape()
        if (shape == null)
          throw new DMLRuntimeException("Didnot expect weights for the layer " + layer.getName)
        if (caffe2DMLLayer.isInstanceOf[DeConvolution]) {
          val data = blobs(0).getDataList
          validateShape(shape, data, layer.getName)
          // Swap dimensions: Caffe's format (F, C*Hf*Wf) to NN layer's format (C, F*Hf*Wf).
          val deconvLayer = caffe2DMLLayer.asInstanceOf[DeConvolution]
          val C           = shape(0)
          val F           = deconvLayer.numKernels.toInt
          val Hf          = deconvLayer.kernel_h.toInt
          val Wf          = deconvLayer.kernel_w.toInt
          val ret1        = allocateDeconvolutionWeight(data, F, C, Hf, Wf)
          asyncThreads.add(ret1._2)
          inputVariables.put(caffe2DMLLayer.weight, ret1._1)
        } else {
          inputVariables.put(caffe2DMLLayer.weight, getMBFromBlob(blobs(0), shape, layer.getName, transpose, asyncThreads))
        }

        // bias
        val biasShape = caffe2DMLLayer.biasShape()
        if (biasShape == null)
          throw new DMLRuntimeException("Didnot expect bias for the layer " + layer.getName)
        inputVariables.put(caffe2DMLLayer.bias, getMBFromBlob(blobs(1), biasShape, layer.getName, transpose, asyncThreads))
        Caffe2DML.LOG.debug("Read weights/bias for layer:" + layer.getName)
      } else if (blobs.size == 1) {
        // Special case: convolution/deconvolution without bias
        // TODO: Extend nn layers to handle this situation + Generalize this to other layers, for example: InnerProduct
        val caffe2DMLLayer = net.getCaffeLayer(layer.getName)
        val convParam =
          if ((caffe2DMLLayer.isInstanceOf[Convolution] || caffe2DMLLayer.isInstanceOf[DeConvolution]) && caffe2DMLLayer.param.hasConvolutionParam())
            caffe2DMLLayer.param.getConvolutionParam
          else null
        if (convParam == null)
          throw new DMLRuntimeException("Layer with blob count " + layer.getBlobsCount + " is not supported for the layer " + layer.getName)
        else if (convParam.hasBiasTerm && convParam.getBiasTerm)
          throw new DMLRuntimeException("Layer with blob count " + layer.getBlobsCount + " and with bias term is not supported for the layer " + layer.getName)

        inputVariables.put(caffe2DMLLayer.weight, getMBFromBlob(blobs(0), caffe2DMLLayer.weightShape(), layer.getName, false, asyncThreads))
        inputVariables.put(caffe2DMLLayer.bias, new MatrixBlock(convParam.getNumOutput, 1, false))
        Caffe2DML.LOG.debug("Read only weight for layer:" + layer.getName)
      } else {
        throw new DMLRuntimeException("Layer with blob count " + layer.getBlobsCount + " is not supported for the layer " + layer.getName)
      }
    }

    // Wait for the copy to be finished
    for (t <- asyncThreads) {
      t.join()
    }

    for (mb <- inputVariables.values()) {
      mb.recomputeNonZeros();
    }

    // Return the NetParameter without
    return readCaffeNet(netFilePath)
  }

  def getBlobs(layer: LayerParameter, v1Layers: scala.collection.immutable.Map[String, caffe.Caffe.V1LayerParameter]): java.util.List[caffe.Caffe.BlobProto] =
    if (layer.getBlobsCount != 0)
      layer.getBlobsList
    else if (v1Layers.contains(layer.getName)) v1Layers.get(layer.getName).get.getBlobsList
    else null

  def getMBFromBlob(blob: caffe.Caffe.BlobProto,
                    shape: Array[Int],
                    layerName: String,
                    transpose: Boolean,
                    asyncThreads: java.util.ArrayList[CopyFloatToDoubleArray]): MatrixBlock = {
    val data = blob.getDataList
    validateShape(shape, data, layerName)
    val ret1 = allocateMatrixBlock(data, shape(0), shape(1), transpose)
    asyncThreads.add(ret1._2)
    return ret1._1
  }

  def readCaffeSolver(solverFilePath: String): SolverParameter = {
    val reader  = getInputStreamReader(solverFilePath);
    val builder = SolverParameter.newBuilder();
    TextFormat.merge(reader, builder);
    return builder.build();
  }

  // --------------------------------------------------------------
  // File IO utility functions
  def writeToFile(content: String, filePath: String): Unit = {
    val pw = new java.io.PrintWriter(new File(filePath))
    pw.write(content)
    pw.close
  }
  def getInputStreamReader(filePath: String): InputStreamReader = {
    //read solver script from file
    if (filePath == null)
      throw new LanguageException("file path was not specified!");
    if (filePath.startsWith("hdfs:") || filePath.startsWith("gpfs:")) {
      val fs = FileSystem.get(ConfigurationManager.getCachedJobConf());
      return new InputStreamReader(fs.open(new Path(filePath)));
    } else {
      return new InputStreamReader(new FileInputStream(new File(filePath)), "ASCII");
    }
  }
  // --------------------------------------------------------------
  
  // Returns the memory requirement for the layer in number of bytes
  def getMemInBytes(l:CaffeLayer, batchSize:Int, isTraining:Boolean):Long = {
    val numLayerInput =  if(!l.isInstanceOf[Data]) l.bottomLayerOutputShape._1.toLong * l.bottomLayerOutputShape._2.toLong * l.bottomLayerOutputShape._3.toLong  * batchSize else 0
    val numLayerOutput = l.outputShape._1.toLong * l.outputShape._2.toLong * l.outputShape._3.toLong  * batchSize
    val numLayerError = numLayerOutput
    val numLayerWeights = if(l.weightShape != null) {
      val nWt = l.weightShape()(0).toLong * l.weightShape()(1).toLong
      if(l.extraWeightShape != null) l.extraWeightShape()(0).toLong * l.extraWeightShape()(1).toLong + nWt
      else nWt
    } else 0
    val numLayerBias = if(l.biasShape != null)l.biasShape()(0).toLong * l.biasShape()(1).toLong else 0
    val numLayerGradients = (numLayerWeights + numLayerBias) * batchSize
    if(isTraining) (numLayerInput + numLayerOutput + numLayerError + numLayerWeights + numLayerBias + numLayerGradients)*java.lang.Double.BYTES
    else (numLayerInput + numLayerOutput + numLayerWeights + numLayerBias)*java.lang.Double.BYTES
  }
}

class Utils {
  def saveCaffeModelFile(sc: JavaSparkContext, deployFilePath: String, caffeModelFilePath: String, outputDirectory: String, format: String): Unit =
    Utils.saveCaffeModelFile(sc, deployFilePath, caffeModelFilePath, outputDirectory, format)

}
