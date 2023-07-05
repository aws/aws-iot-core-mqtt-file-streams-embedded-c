#ifndef MQTT_FILE_DOWNLOADER_H
#define MQTT_FILE_DOWNLOADER_H


 /* MQTT library includes. */
#include "core_mqtt.h"

 /**
  * Initializes the MQTT file downloader.
  * Creates the topic name the DATA and Get Stream Data topics
  *
  * @param[in] pxMQTTContext MQTT context pointer.
  * @param[in] pStreamName Stream name to download the file.
  * @param[in] pThingName Thing name of the Device.
  */
uint8_t ucMqttFileDownloaderInit(MQTTContext_t * pxMQTTContext, char * pStreamName, char *pThingName);

/**
 * Request the Data blocks from MQTT Streams.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 * @param[in] usFileId File Id of the file to be downloaded from MQTT Streams.
 * @param[in] ulBlockSize Requested size of block.
 * @param[in] usBlockOffset Block Offset.
 * @param[in] ulNumberOfBlocksRequested Number of Blocks requested per request.
 */
uint8_t ucRequestDataBlock(MQTTContext_t* pxMQTTContext, uint16_t usFileId,
                                                        uint32_t ulBlockSize,
                                                        uint16_t usBlockOffset,
                                                        uint32_t ulNumberOfBlocksRequested);

/**
 * @brief Process incoming Publish message.
 *
 * @param[in] pxPublishInfo is a pointer to structure containing deserialized
 * Publish message.
 */
void prvMQTTProcessIncomingPublish(MQTTPublishInfo_t* pxPublishInfo);

/**
 * @brief Function to update variable TopicFilterContext with status
 * information from Subscribe ACK. Called by the event callback after processing
 * an incoming SUBACK packet.
 *
 * @param[in] Server response to the subscription request.
 */
void prvUpdateSubAckStatus(MQTTPacketInfo_t* pxPacketInfo);

#endif // #ifndef MQTT_FILE_DOWNLOADER_H

 