---
layout: global
title: SystemML Release Process
description: Description of the SystemML release process and validation.
displayTitle: SystemML Release Process
---
<!--
{% comment %}
Licensed to the Apache Software Foundation (ASF) under one or more
contributor license agreements.  See the NOTICE file distributed with
this work for additional information regarding copyright ownership.
The ASF licenses this file to you under the Apache License, Version 2.0
(the "License"); you may not use this file except in compliance with
the License.  You may obtain a copy of the License at

http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
{% endcomment %}
-->

* This will become a table of contents (this text will be scraped).
{:toc}


# Snapshot Deployment

The following instructions describe how to deploy artifacts to the Apache Snapshot Repository during development.

## Snapshot Deployment Setup

**Maven Password Encryption**

Follow the instructions at [https://maven.apache.org/guides/mini/guide-encryption.html](https://maven.apache.org/guides/mini/guide-encryption.html).

**Create an Encrypted Master Password**

```
mvn --encrypt-master-password
```

This will generate an encrypted password. Create a `settings-security.xml` file at `~/.m2/settings-security.xml` if it doesn't exist.
Add the encrypted master password to this file.

```
<settingsSecurity>
  <master>{ENCRYPTED_PASSWORD_GOES_HERE}</master>
</settingsSecurity>
```

**Create an Encrypted Version of your Apache Password**

```
mvn --encrypt-password
```

Add a server entry to your `~/.m2/settings.xml` file (create this file if it doesn't already exist). This server entry will have the
Apache Snapshot ID, your Apache ID, and your encrypted password.

```
<settings>
  <servers>
    <server>
      <id>apache.snapshots.https</id>
      <username>YOUR_APACHE_ID</username>
      <password>{ENCRYPTED_PASSWORD_GOES_HERE}</password>
    </server>
  </servers>
</settings>
```

**Install and Configure GPG**

On OS X, download GPG from [https://gpgtools.org/](https://gpgtools.org/). One such release is
[https://releases.gpgtools.org/GPG_Suite-2016.08_v2.dmg](https://releases.gpgtools.org/GPG_Suite-2016.08_v2.dmg).

Install GPG.

Generate a public/private key pair. For example, you can use your name and Apache email.

```
gpg --gen-key
```

Your public and private keys can be verified using:

```
gpg --list-keys
gpg --list-secret-keys
```

**Clone SystemML Repository**

Since the artifacts will be deployed publicly, you should ensure that the project is completely clean.
The deploy command should not be run on a copy of the project that you develop on. It should be a completely
clean project used only for building and deploying.

Therefore, create a directory such as:

```
mkdir ~/clean-systemml
```

In that directory, clone a copy of the project.

```
git clone https://github.com/apache/systemml.git
```


## Deploy Artifacts to Snapshot Repository

Before deploying the latest snapshot artifacts, ensure you have the latest code on the master branch.

```
git pull
```

In the `pom.xml` file, the `maven-gpg-plugin`'s `sign` goal is bound to the `verify` stage of the Maven lifecycle.
Therefore, you can check that signing works by installing the snapshot to your local Maven repository.

```
mvn clean install -DskipTests -Pdistribution
```

If this succeeds, you can deploy the snapshot artifacts to the Apache Snapshot Repository using the following:

```
mvn clean deploy -DskipTests -Pdistribution
```

Verify that the snapshot is now available at
[https://repository.apache.org/content/repositories/snapshots/org/apache/systemml/systemml](https://repository.apache.org/content/repositories/snapshots/org/apache/systemml/systemml).


# Release Candidate Build and Deployment

For detailed information, please see [SystemML Release Creation Process](release-creation-process.html).

# Release Candidate Checklist

## All Artifacts and Checksums Present

<a href="#release-candidate-checklist">Up to Checklist</a>

Verify that each expected artifact is present at [https://dist.apache.org/repos/dist/dev/systemml/](https://dist.apache.org/repos/dist/dev/systemml/) and that each artifact has accompanying
checksums (such as .asc and .md5).


## Release Candidate Build

<a href="#release-candidate-checklist">Up to Checklist</a>

The release candidate should build on Windows, OS X, and Linux. To do this cleanly,
the following procedure can be performed.

Clone the Apache SystemML GitHub repository
to an empty location. Next, check out the release tag. Following
this, build the distributions using Maven. This should be performed
with an empty local Maven repository.

Here is an example:

	$ git clone https://github.com/apache/systemml.git
	$ cd systemml
	$ git tag -l
	$ git checkout tags/1.0.0-rc1 -b 1.0.0-rc1
	$ mvn -Dmaven.repo.local=$HOME/.m2/temp-repo clean package -P distribution


## Test Suite Passes

<a href="#release-candidate-checklist">Up to Checklist</a>

The entire test suite should pass on Windows, OS X, and Linux.
The test suite can be run using:

	$ mvn clean verify


## All Binaries Execute

<a href="#release-candidate-checklist">Up to Checklist</a>

Validate that all of the binary artifacts can execute, including those artifacts packaged
in other artifacts (in the tgz and zip artifacts).

The build artifacts should be downloaded from [https://dist.apache.org/repos/dist/dev/systemml/](https://dist.apache.org/repos/dist/dev/systemml/) and these artifacts should be tested, as in
this OS X example.

	# download artifacts
	wget -r -nH -nd -np -R 'index.html*' https://dist.apache.org/repos/dist/dev/systemml/1.0.0-rc1/

	# verify standalone tgz works
	tar -xvzf systemml-1.0.0-bin.tgz
	cd systemml-1.0.0-bin
	echo "print('hello world');" > hello.dml
	./runStandaloneSystemML.sh hello.dml
	cd ..

	# verify standalone zip works
	rm -rf systemml-1.0.0-bin
	unzip systemml-1.0.0-bin.zip
	cd systemml-1.0.0-bin
	echo "print('hello world');" > hello.dml
	./runStandaloneSystemML.sh hello.dml
	cd ..

	# verify src works
	tar -xvzf systemml-1.0.0-src.tgz
	cd systemml-1.0.0-src
	mvn clean package -P distribution
	cd target/
	java -cp "./lib/*:systemml-1.0.0.jar" org.apache.sysml.api.DMLScript -s "print('hello world');"
	java -cp "./lib/*:SystemML.jar" org.apache.sysml.api.DMLScript -s "print('hello world');"
	cd ../..

	# verify spark batch mode
	export SPARK_HOME=~/spark-2.1.0-bin-hadoop2.7
	cd systemml-1.0.0-bin/target/lib
	$SPARK_HOME/bin/spark-submit systemml-1.0.0.jar -s "print('hello world');" -exec hybrid_spark

	# verify hadoop batch mode
	hadoop jar systemml-1.0.0.jar -s "print('hello world');"


	# verify python artifact
	# install numpy, pandas, scipy & set SPARK_HOME
	pip install numpy
	pip install pandas
	pip install scipy
	export SPARK_HOME=~/spark-2.1.0-bin-hadoop2.7
	# get into the pyspark prompt
	cd systemml-1.0.0
	$SPARK_HOME/bin/pyspark --driver-class-path systemml-java/systemml-1.0.0.jar
	# Use this program at the prompt:
	import systemml as sml
	import numpy as np
	m1 = sml.matrix(np.ones((3,3)) + 2)
	m2 = sml.matrix(np.ones((3,3)) + 3)
	m2 = m1 * (m2 + m1)
	m4 = 1.0 - m2
	m4.sum(axis=1).toNumPy()

	# This should be printed
	# array([[-60.],
	#       [-60.],
	#       [-60.]])



## Python Tests

For Spark 1.*, the Python tests at (`src/main/python/tests`) can be executed in the following manner:

	PYSPARK_PYTHON=python3 pyspark --driver-class-path SystemML.jar test_matrix_agg_fn.py
	PYSPARK_PYTHON=python3 pyspark --driver-class-path SystemML.jar test_matrix_binary_op.py
	PYSPARK_PYTHON=python3 pyspark --driver-class-path SystemML.jar test_mlcontext.py
	PYSPARK_PYTHON=python3 pyspark --driver-class-path SystemML.jar test_mllearn_df.py
	PYSPARK_PYTHON=python3 pyspark --driver-class-path SystemML.jar test_mllearn_numpy.py

For Spark 2.*, pyspark can't be used to run the Python tests, so they can be executed using
spark-submit:

	spark-submit --driver-class-path SystemML.jar test_matrix_agg_fn.py
	spark-submit --driver-class-path SystemML.jar test_matrix_binary_op.py
	spark-submit --driver-class-path SystemML.jar test_mlcontext.py
	spark-submit --driver-class-path SystemML.jar test_mllearn_df.py
	spark-submit --driver-class-path SystemML.jar test_mllearn_numpy.py


## Check LICENSE and NOTICE Files

<a href="#release-candidate-checklist">Up to Checklist</a>

Each artifact *must* contain LICENSE and NOTICE files. These files must reflect the
contents of the artifacts. If the project dependencies (ie, libraries) have changed
since the last release, the LICENSE and NOTICE files must be updated to reflect these
changes.

For more information, see:

1. <http://www.apache.org/dev/#releases>
2. <http://www.apache.org/dev/licensing-howto.html>


## Src Artifact Builds and Tests Pass

<a href="#release-candidate-checklist">Up to Checklist</a>

The project should be built using the `src` (tgz and zip) artifacts.
In addition, the test suite should be run using an `src` artifact and
the tests should pass.

	tar -xvzf systemml-1.0.0-src.tgz
	cd systemml-1.0.0-src
	mvn clean package -P distribution
	mvn verify


## Single-Node Standalone

<a href="#release-candidate-checklist">Up to Checklist</a>

The standalone tgz and zip artifacts contain `runStandaloneSystemML.sh` and `runStandaloneSystemML.bat`
files. Verify that one or more algorithms can be run on a single node using these
standalone distributions.

Here is an example based on the [Standalone Guide](http://apache.github.io/systemml/standalone-guide.html)
demonstrating the execution of an algorithm (on OS X).

	tar -xvzf systemml-1.0.0-bin.tgz
	cd systemml-1.0.0-bin
	wget -P data/ http://archive.ics.uci.edu/ml/machine-learning-databases/haberman/haberman.data
	echo '{"rows": 306, "cols": 4, "format": "csv"}' > data/haberman.data.mtd
	echo '1,1,1,2' > data/types.csv
	echo '{"rows": 1, "cols": 4, "format": "csv"}' > data/types.csv.mtd
	./runStandaloneSystemML.sh scripts/algorithms/Univar-Stats.dml -nvargs X=data/haberman.data TYPES=data/types.csv STATS=data/univarOut.mtx CONSOLE_OUTPUT=TRUE
	cd ..


## Single-Node Spark

<a href="#release-candidate-checklist">Up to Checklist</a>

Verify that SystemML runs algorithms on Spark locally.

Here is an example of running the `Univar-Stats.dml` algorithm on random generated data.

	cd systemml-1.0.0-bin/lib
	export SPARK_HOME=~/spark-2.1.0-bin-hadoop2.7
	$SPARK_HOME/bin/spark-submit systemml-1.0.0.jar -f ../scripts/datagen/genRandData4Univariate.dml -exec hybrid_spark -args 1000000 100 10 1 2 3 4 uni.mtx
	echo '1' > uni-types.csv
	echo '{"rows": 1, "cols": 1, "format": "csv"}' > uni-types.csv.mtd
	$SPARK_HOME/bin/spark-submit systemml-1.0.0.jar -f ../scripts/algorithms/Univar-Stats.dml -exec hybrid_spark -nvargs X=uni.mtx TYPES=uni-types.csv STATS=uni-stats.txt CONSOLE_OUTPUT=TRUE
	cd ..


## Single-Node Hadoop

<a href="#release-candidate-checklist">Up to Checklist</a>

Verify that SystemML runs algorithms on Hadoop locally.

Based on the "Single-Node Spark" setup above, the `Univar-Stats.dml` algorithm could be run as follows:

	cd systemml-1.0.0-bin/lib
	hadoop jar systemml-1.0.0.jar -f ../scripts/algorithms/Univar-Stats.dml -nvargs X=uni.mtx TYPES=uni-types.csv STATS=uni-stats.txt CONSOLE_OUTPUT=TRUE


## Notebooks

<a href="#release-candidate-checklist">Up to Checklist</a>

Verify that SystemML can be executed from Jupyter and Zeppelin notebooks.
For examples, see the [Spark MLContext Programming Guide](http://apache.github.io/systemml/spark-mlcontext-programming-guide.html).


## Performance Suite

<a href="#release-candidate-checklist">Up to Checklist</a>

Verify that the performance suite executes on Spark and Hadoop. Testing should
include 80MB, 800MB, 8GB, and 80GB data sizes.

For more information, please see [SystemML Performance Testing](python-performance-test.html).


# Run NN Unit Tests for GPU

<a href="#release-candidate-checklist">Up to Checklist</a>

The unit tests for NN operators for GPU take a long time to run and are therefore not run as part of the Jenkins build.
They must be run before a release. To run them, edit the
[NeuralNetworkOpTests.java](https://github.com/apache/systemml/blob/master/src/test/java/org/apache/sysml/test/gpu/NeuralNetworkOpTests.java)
file and remove all the `@Ignore` annotations from all the tests. Then run the NN unit tests using mvn verify:

	mvn -Dit.test=org.apache.sysml.test.gpu.NeuralNetworkOpTests verify -PgpuTests


# Voting

Following a successful release candidate vote by SystemML PMC members on the SystemML mailing list, the release candidate
has been approved.


# Release


## Release Deployment

To be written. (What steps need to be done? How is the release deployed to Apache dist and the central maven repo?
Where do the release notes for the release go?)


## Documentation Deployment

This section describes how to deploy versioned project documentation to the main website.
Note that versioned project documentation is committed directly to the `svn` project's `docs` folder.
The versioned project documentation is not committed to the website's `git` project.

Checkout branch in main project (`systemml`).

	$ git checkout branch-1.0.0

In `systemml/docs/_config.yml`, set:

* `SYSTEMML_VERSION` to project version (1.0.0)
* `FEEDBACK_LINKS` to `false` (only have feedback links on `LATEST` docs)
* `API_DOCS_MENU` to `true` (adds `API Docs` menu to get to project javadocs)

Generate `docs/_site` by running `bundle exec jekyll serve` in `systemml/docs`.

	$ bundle exec jekyll serve

Verify documentation site looks correct.

In website `svn` project, create `systemml-website-site/docs/1.0.0` folder.

Copy contents of `systemml/docs/_site` to `systemml-website-site/docs/1.0.0`.

Delete any unnecessary files (`Gemfile`, `Gemfile.lock`).

Create `systemml-website-site/docs/1.0.0/api/java` folder for javadocs.
Create `systemml-website-site/docs/1.0.0/api/python` folder for pythondocs.

Update `systemml/pom.xml` project version to what should be displayed in javadocs (such as `1.0.0`).

Build project (which generates javadocs).

	$ mvn clean package -P distribution

Copy contents of `systemml/target/apidocs` to `systemml-website-site/docs/1.0.0/api/java`.

Define environment variables to match version and release number used in updated `systemml/pom.xml`.  Both environment variables are referenced when building pythondocs with Sphinx.

	$ export SYSTEMML_VERSION=1.0
	$ export SYSTEMML_RELEASE=1.0.0

Generate pythondocs with Sphinx.

	$ cd systemml/src/main/pythondoc
	$ make html

Copy contents of `systemml/target/pydocs/html` to `systemml-website-site/docs/1.0.0/api/python`.

Open up `file:///.../systemml-website-site/docs/1.0.0/index.html` and verify `API Docs` &rarr; `Java` link works and that the correct Javadoc version is displayed.
Verify `API Docs` &rarr; `Python` link works and that the same Pythondoc version is displayed. Verify feedback links under `Issues` menu are not present.

Clean up any unnecessary files (such as deleting `.DS_Store` files on OS X).

	$ find . -name '.DS_Store' -type f -delete

Commit the versioned project documentation to `svn`:

	$ svn status
	$ svn add docs/1.0.0
	$ svn commit -m "Add 1.0.0 docs to website"

Update `systemml-website/_src/documentation.html` to include 1.0.0 link.

Start main website site by running `gulp` in `systemml-website`:

	$ gulp

Commit and push the update to `git` project.

	$ git add -u
	$ git commit -m "Add 1.0.0 link to documentation page"
	$ git push
	$ git push apache master

Copy contents of `systemml-website/_site` (generated by `gulp`) to `systemml-website-site`.
After doing so, we should see that `systemml-website-site/documentation.html` has been updated.

	$ svn status
	$ svn diff

Commit the update to `documentation.html` to publish the website update.

	$ svn commit -m "Add 1.0.0 link to documentation page"

The versioned project documentation is now deployed to the main website, and the
[Documentation Page](http://systemml.apache.org/documentation) contains a link to the versioned documentation.
