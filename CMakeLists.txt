cmake_minimum_required(VERSION 3.15)

project(AwsMQTTFileStreams LANGUAGES C)

# ------------------------------------------------------------------------------
# Includes
# ------------------------------------------------------------------------------

include(${CMAKE_CURRENT_LIST_DIR}/mqttFileDownloaderFilePaths.cmake)

# ------------------------------------------------------------------------------
# Library targets
# ------------------------------------------------------------------------------

add_library( aws_mqtt_file_streams )


target_sources( aws_mqtt_file_streams PUBLIC ${MQTT_FILE_DOWNLOADER_SOURCES} )

target_include_directories( aws_mqtt_file_streams PUBLIC ${MQTT_FILE_DOWNLOADER_INCLUDES} )


if(STANDALONE_TEST_BUILD_UNIX)
    include(FetchContent)
    FetchContent_Declare(
    CoreJSON
    GIT_REPOSITORY https://github.com/FreeRTOS/coreJSON.git
    GIT_TAG cffa492da18c890181d64462f8af63992a69d3b0)

    FetchContent_Declare(
    tinycbor
    # hash: sha256-otueOD8tkzbHHVuOBI6krewYoeteRGAAQWSf0r19P5s=
    GIT_REPOSITORY https://github.com/intel/tinycbor.git
    GIT_TAG 9924cfed3b95ad6de299ae675064430fdb886216)

    FetchContent_MakeAvailable(CoreJSON tinycbor)

    # Add coreJSON library
    include("${corejson_SOURCE_DIR}/jsonFilePaths.cmake")
    add_library(coreJSON ${JSON_SOURCES})
    target_include_directories(coreJSON PUBLIC ${JSON_INCLUDE_PUBLIC_DIRS})

    # tinycbor
    add_library(
    tinycbor
    "${tinycbor_SOURCE_DIR}/src/cborparser.c"
    "${tinycbor_SOURCE_DIR}/src/cborencoder.c"
    "${tinycbor_SOURCE_DIR}/src/cborencoder_close_container_checked.c")
    target_include_directories(tinycbor PUBLIC "${tinycbor_SOURCE_DIR}/src")

    target_link_libraries(aws_mqtt_file_streams PUBLIC coreJSON tinycbor)

    target_compile_definitions(aws_mqtt_file_streams PUBLIC MQTT_STREAMS_DO_NOT_USE_CUSTOM_CONFIG=1)

    message(WARNING "This is a test build with default configs and pre-set coreJSON and tinycbor sources. "
                    "Please do not use this in production code as is before verifying that this is what you need.")
endif()