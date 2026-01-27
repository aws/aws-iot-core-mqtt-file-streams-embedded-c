cmake_minimum_required(VERSION 3.15)

project(aws-iot-core-mqtt-file-streams LANGUAGES C)

# ------------------------------------------------------------------------------
# Includes
# ------------------------------------------------------------------------------

include(${CMAKE_CURRENT_LIST_DIR}/mqttFileDownloaderFilePaths.cmake)

# ------------------------------------------------------------------------------
# Library targets
# ------------------------------------------------------------------------------

add_library(aws_iot_core_mqtt_file_streams INTERFACE)

target_sources(aws_iot_core_mqtt_file_streams INTERFACE ${MQTT_FILE_DOWNLOADER_SOURCES})

target_include_directories(aws_iot_core_mqtt_file_streams INTERFACE ${MQTT_FILE_DOWNLOADER_INCLUDES})

message(STATUS "aws_iot_core_mqtt_file_streams library requires coreJSON and tinycbor as dependencies.")
