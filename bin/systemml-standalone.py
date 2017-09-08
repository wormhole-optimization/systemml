#!/usr/bin/env python
#-------------------------------------------------------------
#
# Licensed to the Apache Software Foundation (ASF) under one
# or more contributor license agreements.  See the NOTICE file
# distributed with this work for additional information
# regarding copyright ownership.  The ASF licenses this file
# to you under the Apache License, Version 2.0 (the
# "License"); you may not use this file except in compliance
# with the License.  You may obtain a copy of the License at
#
#   http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing,
# software distributed under the License is distributed on an
# "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY
# KIND, either express or implied.  See the License for the
# specific language governing permissions and limitations
# under the License.
#
#-------------------------------------------------------------

import os
from os.path import join
import argparse
import platform
from utils import get_env_systemml_home, find_dml_file, log4j_path, config_path


def default_classpath(systemml_home):
    """
    Classpath information required for excution

    return: String
    Classpath location of build, library and hadoop directories
    """
    build_lib = join(systemml_home, 'target', '*')
    lib_lib = join(systemml_home, 'target', 'lib', '*')
    hadoop_lib = join(systemml_home, 'target', 'lib', 'hadoop', '*')

    return build_lib, lib_lib, hadoop_lib


#TODO
# User dir, fix for SYSTEMML_1795
def standalone_execution_entry(nvargs, args, config, explain, debug, stats, gpu, heapmem, f):
    """
    This function is responsible for the execution of arguments via
    subprocess call in singlenode mode
    """

    systemml_home = get_env_systemml_home()
    script_file = find_dml_file(systemml_home, f)

    if platform.system() == 'Windows':
        default_cp = ';'.join(default_classpath(systemml_home))
    else:
        default_cp = ':'.join(default_classpath(systemml_home))

    java_memory = '-Xmx' + heapmem + ' -Xms4g -Xmn1g'

    # Log4j
    log4j = log4j_path(systemml_home)
    log4j_properties_path = '-Dlog4j.configuration=file:{}'.format(log4j)

    # Config
    if config is None:
        default_config = config_path(systemml_home)
    else:
        default_config = config

    ml_options = []
    if nvargs is not None:
        ml_options.append('-nvargs')
        ml_options.append(' '.join(nvargs))
    if args is not None:
        ml_options.append('-args')
        ml_options.append(' '.join(args))
    if explain is not None:
        ml_options.append('-explain')
        ml_options.append(explain)
    if debug is not False:
        ml_options.append('-debug')
    if stats is not None:
        ml_options.append('-stats')
        ml_options.append(stats)
    if gpu is not None:
        ml_options.append('-gpu')
        ml_options.append(gpu)

    cmd = ['java', java_memory, log4j_properties_path,
           '-cp', default_cp, 'org.apache.sysml.api.DMLScript',
           '-f', script_file, '-exec', 'singlenode', '-config', default_config,
           ' '.join(ml_options)]

    cmd = ' '.join(cmd)
    print(cmd)

    return_code = os.system(cmd)
    return return_code


if __name__ == '__main__':

    cparser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter,
                                      description='System-ML Standalone Script')

    # SYSTEM-ML Options
    cparser.add_argument('-nvargs', help='List of attributeName-attributeValue pairs', nargs='+', metavar='')
    cparser.add_argument('-args', help='List of positional argument values', metavar='', nargs='+')
    cparser.add_argument('-config', help='System-ML configuration file (e.g SystemML-config.xml)', metavar='')
    cparser.add_argument('-explain', help='explains plan levels can be hops, runtime, '
                                          'recompile_hops, recompile_runtime', nargs='?', const='runtime', metavar='')
    cparser.add_argument('-debug', help='runs in debug mode', action='store_true')
    cparser.add_argument('-stats', help='Monitor and report caching/recompilation statistics, '
                                        'heavy hitter <count> is 10 unless overridden', nargs='?', const='10',
                         metavar='')
    cparser.add_argument('-gpu', help='uses CUDA instructions when reasonable, '
                                      'set <force> option to skip conservative memory estimates '
                                      'and use GPU wherever possible', nargs='?')
    cparser.add_argument('-heapmem', help='maximum JVM heap memory', metavar='', default='8g')
    cparser.add_argument('-f', required=True, help='specifies dml/pydml file to execute; '
                                                   'path can be local/hdfs/gpfs', metavar='')

    args = cparser.parse_args()
    arg_dict = vars(args)
    return_code = standalone_execution_entry(**arg_dict)

    if return_code != 0:
        print('Failed to run SystemML. Exit code :' + str(return_code))
