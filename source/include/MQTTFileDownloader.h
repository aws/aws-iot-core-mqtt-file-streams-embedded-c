/*
 * Copyright Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

#ifndef MQTT_FILE_DOWNLOADER_H
#define MQTT_FILE_DOWNLOADER_H

#include <stdbool.h>
#include <stdint.h>

/**
 *  @brief Topic strings used by the MQTT downloader.
 *
 * These first few are topic extensions to the dynamic base topic that includes
 * the Thing name.
 */
#define MQTT_API_THINGS     "$aws/things/" /*!< Topic prefix for thing APIs. */
#define MQTT_API_STREAMS    "/streams/"    /*!< Stream API identifier. */
#define MQTT_API_DATA_CBOR  "/data/cbor"   /*!< Stream API suffix. */
#define MQTT_API_GET_CBOR   "/get/cbor"    /*!< Stream API suffix. */
#define MQTT_API_DATA_JSON  "/data/json"   /*!< JSON DATA Stream API suffix. */
#define MQTT_API_GET_JSON   "/get/json"    /*!< JSON GET Stream API suffix. */

/* Maximum lengths for constants used in MQTT downloader.
 * These are used to calculate the static size of buffers used to store MQTT
 * topic and message strings. Each length is in terms of bytes. */
#define STREAM_NAME_MAX_LEN 44U
#define NULL_CHAR_LEN       1U
#define MAX_THINGNAME_LEN   128U

#define CONST_STRLEN( s )   ( ( ( uint32_t ) sizeof( s ) ) - 1UL )

#define TOPIC_COMMON_PARTS_LEN                              \
    ( CONST_STRLEN( MQTT_API_THINGS ) + MAX_THINGNAME_LEN + \
      CONST_STRLEN( MQTT_API_STREAMS ) + STREAM_NAME_MAX_LEN + NULL_CHAR_LEN )

#define TOPIC_STREAM_DATA_BUFFER_SIZE \
    ( TOPIC_COMMON_PARTS_LEN + CONST_STRLEN( MQTT_API_DATA_CBOR ) )

#define TOPIC_GET_STREAM_BUFFER_SIZE \
    ( TOPIC_COMMON_PARTS_LEN + CONST_STRLEN( MQTT_API_GET_CBOR ) )

#define GET_STREAM_REQUEST_BUFFER_SIZE       256U
/*
 * Configure the Maximum size of the data payload.
 */
#define mqttFileDownloader_CONFIG_BLOCK_SIZE 256U
/*
 * @brief  MQTT File Downloader return codes.
 */
typedef enum
{
    MQTTFileDownloaderSuccess,
    MQTTFileDownloaderBadParameter,
    MQTTFileDownloaderNotInitialized,
    MQTTFileDownloaderInitFailed,
    MQTTFileDownloaderSubscribeFailed,
    MQTTFileDownloaderPublishFailed,
    MQTTFileDownloaderDataDecodingFailed
} MQTTFileDownloaderStatus_t;

/*
 * Enum contains all the data types supported.
 */
typedef enum
{
    DATA_TYPE_JSON,
    DATA_TYPE_CBOR
} DataType_t;

typedef struct
{
    char topicStreamData[ TOPIC_STREAM_DATA_BUFFER_SIZE ];
    size_t topicStreamDataLength;
    char topicGetStream[ TOPIC_GET_STREAM_BUFFER_SIZE ];
    size_t topicGetStreamLength;
    DataType_t dataType;
} MqttFileDownloaderContext_t;

/**
 * Initializes the MQTT file downloader.
 * Creates the topic name the DATA and Get Stream Data topics
 *
 * @param[in] context MQTT file downloader context pointer.
 * @param[in] streamName Stream name to download the file.
 * @param[in] streamNameLength Length of the Stream name to download the file.
 * @param[in] thingName Thing name of the Device.
 * @param[in] thingNameLength Length of the Thing name of the Device.
 * @param[in] dataType Either JSON or CBOR data type.
 *
 * @return MQTTFileDownloaderStatus_t returns appropriate MQTT File Downloader Status.
 */
MQTTFileDownloaderStatus_t mqttDownloader_init( MqttFileDownloaderContext_t * context,
                             const char * streamName,
                             size_t streamNameLength,
                             const char * thingName,
                             size_t thingNameLength,
                             DataType_t dataType );

/**
 * Creates the get request for Data blocks from MQTT Streams.
 *
 * @param[in] dataType Either JSON or CBOR data type.
 * @param[in] fileId File Id of the file to be downloaded from MQTT Streams.
 * @param[in] blockSize Requested size of block.
 * @param[in] blockOffset Block Offset.
 * @param[in] numberOfBlocksRequested Number of Blocks requested per request.
 * @param[out] getStreamRequest Buffer to store the get stream request.
 *
 * @return size_t returns Length of the get stream request.
 */
size_t mqttDownloader_createGetDataBlockRequest(
    DataType_t dataType,
    uint16_t fileId,
    uint32_t blockSize,
    uint16_t blockOffset,
    uint32_t numberOfBlocksRequested,
    char * getStreamRequest,
    size_t getStreamRequestLength);

/**
 * @brief Checks if the incoming Publish message contains MQTT Data block.
 *
 * @param[in] context MQTT file downloader context pointer.
 * @param[in] topic incoming Publish message MQTT topic.
 * @param[in] topicLength incoming Publish message MQTT topic length.
 *
 * @return returns True if the message contains Data block else False.
 */
bool mqttDownloader_isDataBlockReceived( const MqttFileDownloaderContext_t * context,
                                                               const char * topic,
                                                               size_t topicLength );

/**
 * @brief Process incoming Publish message.
 *
 * @param[in] context MQTT file downloader context pointer.
 * Publish message.
 *
 * @return returns True if the message is handled else False.
 */
bool mqttDownloader_processReceivedDataBlock(
    const MqttFileDownloaderContext_t * context,
    uint8_t * message,
    size_t messageLength,
    uint8_t * data,
    size_t * dataLength );

#endif /* #ifndef MQTT_FILE_DOWNLOADER_H */
