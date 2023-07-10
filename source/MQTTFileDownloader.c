/*
License Info
 */

/* Standard includes. */
#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include <stdint.h>
#include <string.h>
#include <assert.h>

#include "MQTTFileDownloader.h"
#include "core_json.h"

/* Logging configuration for the library. */
#ifndef LIBRARY_LOG_NAME
#define LIBRARY_LOG_NAME    "MqttFileDownloader"
#endif

#ifndef LIBRARY_LOG_LEVEL
#define LIBRARY_LOG_LEVEL    LOG_DEBUG
#endif

/**
 * @brief The number of topic filters to subscribe.
 */
#define mqttFileDownloaderSubscribeTOPIC_COUNT                            ( 1 )

 /**
  * @brief The number of topic filters to subscribe.
  */
#define mqttFileDownloaderSubscribeRETRY_COUNT                            ( 5 )

 /**
  * @brief Timeout for MQTT_ProcessLoop in milliseconds.
  */
#define mqttFileDownloaderPROCESS_LOOP_TIMEOUT_MS                ( 500U )

  /**
   * @brief Build a string from a set of strings
   *
   * @param[in] pBuffer Buffer to place the output string in.
   * @param[in] bufferSizeBytes Size of the buffer pointed to by pBuffer.
   * @param[in] strings NULL-terminated array of string pointers.
   * @return size_t Length of the output string, not including the terminator.
   */
static size_t stringBuilder(char* pBuffer, size_t bufferSizeBytes, const char* const strings[]);

/**
 * @brief Call #MQTT_ProcessLoop in a loop for the duration of a timeout or
 * #MQTT_ProcessLoop returns a failure.
 *
 * @param[in] pMqttContext MQTT context pointer.
 * @param[in] ulTimeoutMs Duration to call #MQTT_ProcessLoop for.
 *
 * @return Returns the return value of the last call to #MQTT_ProcessLoop.
 */
// static MQTTStatus_t prvProcessLoopWithTimeout(MQTTContext_t* pMqttContext,
//     uint32_t ulTimeoutMs);

/**
 * @brief Subscribes to the topic as specified in pTopicName.
 * In the case of a Subscribe ACK failure, then subscription is
 * retried using an exponential backoff strategy with jitter.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 */
//static bool prvMQTTSubscribeWithRetries(MQTTContext_t* pxMQTTContext, char* pTopicName);
extern bool mqttSubscribe( char * topic, size_t topicLength );

/**
 * @brief Publishes a message mqttexampleMESSAGE on mqttexampleTOPIC topic.
 *
 * @param[in] pxMQTTContext MQTT context pointer.
 */
//void prvMQTTPublishToTopic(MQTTContext_t* pxMQTTContext, char* pTopicName, char* pMessage);
extern bool mqttPublish( char * topic,
                  size_t topicLength,
                  uint8_t * message,
                  size_t messageLength );

extern void otaDemo_handleMqttStreamsBlockArrived( MqttFileDownloaderDataBlockInfo_t *dataBlock );

 /**
  * @brief Packet Identifier generated when Subscribe request was sent to the broker;
  * it is used to match received Subscribe ACK to the transmitted Subscribe packet.
  */
//static uint16_t usDataTopicSubscribePacketIdentifier;

/**
 * @brief Packet Identifier generated when Publish request was sent to the broker;
 * it is used to match received Publish ACK to the transmitted Publish packet.
 */
//static uint16_t usGetDataPublishPacketIdentifier;

/**
 * @brief A pair containing a topic filter and its SUBACK status.
 */
// typedef struct topicFilterContext
// {
//     const char* pcTopicFilter;
//     MQTTSubAckStatus_t xSubAckStatus;
// } topicFilterContext_t;

/**
 * @brief An array containing the context of a SUBACK; the SUBACK status
 * of a filter is updated when the event callback processes a SUBACK.
 */
//static topicFilterContext_t xDataTopicFilterContext;

/**
 *  @brief Topic strings used by the MQTT downloader.
 *
 * These first few are topic extensions to the dynamic base topic that includes the Thing name.
 */
#define MQTT_API_THINGS                       "$aws/things/"          /*!< Topic prefix for thing APIs. */
#define MQTT_API_STREAMS                      "/streams/"             /*!< Stream API identifier. */
#define MQTT_API_DATA_CBOR                    "/data/cbor"            /*!< Stream API suffix. */
#define MQTT_API_GET_CBOR                     "/get/cbor"             /*!< Stream API suffix. */
#define MQTT_API_DATA_JSON                    "/data/json"            /*!< JSON DATA Stream API suffix. */
#define MQTT_API_GET_JSON                     "/get/json"             /*!< JSON GET Stream API suffix. */

 /* NOTE: The format specifiers in this string are placeholders only; the lengths of these
  * strings are used to calculate buffer sizes.
  */
/* Reserved for CBOR data type*/
//static const char pCborStreamDataTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_DATA_CBOR; /*!< Topic template to receive data over a stream. */
//static const char pCborGetStreamTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_GET_CBOR;   /*!< Topic template to request next data over a stream. */
static const char pJsonStreamDataTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_DATA_JSON; /*!< Topic template to receive data over a stream. */
static const char pJsonGetStreamTopicTemplate[] = MQTT_API_THINGS "%s"MQTT_API_STREAMS "%s"MQTT_API_GET_JSON;   /*!< Topic template to request next data over a stream. */

/* Maximum lengths for constants used in the ota_mqtt_topic_strings templates.
 * These are used to calculate the static size of buffers used to store MQTT
 * topic and message strings. Each length is in terms of bytes. */
#define U32_MAX_LEN            10U                                              /*!< Maximum number of output digits of an unsigned long value. */
#define JOB_NAME_MAX_LEN       128U                                             /*!< Maximum length of the name of job documents received from the server. */
#define STREAM_NAME_MAX_LEN    44U                                              /*!< Maximum length for the name of MQTT streams. */
#define NULL_CHAR_LEN          1U                                               /*!< Size of a single null character use */
#define MAX_THINGNAME_LEN    128U

#define CONST_STRLEN( s )    ( ( ( uint32_t ) sizeof( s ) ) - 1UL )
#define TOPIC_PLUS_THINGNAME_LEN( topic )    ( CONST_STRLEN( topic ) + MAX_THINGNAME_LEN + NULL_CHAR_LEN )
#define TOPIC_JSON_STREAM_DATA_BUFFER_SIZE    ( TOPIC_PLUS_THINGNAME_LEN( pJsonStreamDataTopicTemplate ) + STREAM_NAME_MAX_LEN )                                                              /*!< Max buffer size for `streams/<stream_name>/data/cbor` topic. */
#define TOPIC_JSON_GET_STREAM_BUFFER_SIZE     ( TOPIC_PLUS_THINGNAME_LEN( pJsonGetStreamTopicTemplate ) + STREAM_NAME_MAX_LEN )

#define GET_STREAM_REQUEST_BUFFER_SIZE  128U

 /*
  * Buffer to store the thing name.
  */
static char pMqttDownloaderThingName[MAX_THINGNAME_LEN];

/*
 * Buffer to store the name of the data stream.
 */
static char pMqttDownloaderStreamName[STREAM_NAME_MAX_LEN];

/* 
 * Buffer to store the topic generated for requesting data stream. 
 */
static char pRxStreamTopic[TOPIC_JSON_STREAM_DATA_BUFFER_SIZE];

/*
 * Buffer to store the topic generated for requesting data stream. 
 */
static char pGetStreamTopic[TOPIC_JSON_GET_STREAM_BUFFER_SIZE];      


static size_t stringBuilder(char* pBuffer, size_t bufferSizeBytes, const char* const strings[])
{
    size_t curLen = 0;
    size_t i;
    size_t thisLength = 0;

    pBuffer[0] = '\0';

    for (i = 0; strings[i] != NULL; i++)
    {
        thisLength = strlen(strings[i]);

        /* Assert if there is not enough buffer space. */

        assert((thisLength + curLen + 1U) <= bufferSizeBytes);

        (void)strncat(pBuffer, strings[i], bufferSizeBytes - curLen - 1U);
        curLen += thisLength;
    }

    pBuffer[curLen] = '\0';

    return curLen;
}

uint8_t ucMqttFileDownloaderInit(char * pStreamName, char *pThingName)
{
    uint16_t topicLen = 0;
    
    memset(pMqttDownloaderThingName, '\0', MAX_THINGNAME_LEN);
    memcpy(pMqttDownloaderThingName, pThingName, strlen(pThingName));

    memset(pMqttDownloaderStreamName, '\0', STREAM_NAME_MAX_LEN);
    memcpy(pMqttDownloaderStreamName, pStreamName, strlen(pStreamName));

    /* Initializing DATA topic name */
    
    memset(pRxStreamTopic, '\0', TOPIC_JSON_STREAM_DATA_BUFFER_SIZE);
    
    /* NULL-terminated list of topic string parts. */
    const char* pDataTopicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile time, initialized below. */
        MQTT_API_DATA_JSON,
        NULL
    };

    pDataTopicParts[1] = (const char*)pMqttDownloaderThingName;
    pDataTopicParts[3] = (const char*)pMqttDownloaderStreamName;

    topicLen = (uint16_t)stringBuilder( pRxStreamTopic,
                            sizeof(pRxStreamTopic), pDataTopicParts);

    printf("Data topic is %s\n", pRxStreamTopic);
    
    assert((topicLen > 0U) && (topicLen < sizeof(pRxStreamTopic)));

    /* Initializing Get Stream topic name */
    topicLen = 0;
    memset(pGetStreamTopic, '\0', TOPIC_JSON_GET_STREAM_BUFFER_SIZE);

    const char* pGetStreamTopicParts[] =
    {
        MQTT_API_THINGS,
        NULL, /* Thing Name not available at compile time, initialized below. */
        MQTT_API_STREAMS,
        NULL, /* Stream Name not available at compile time, initialized below. */
        MQTT_API_GET_JSON,
        NULL
    };

    pGetStreamTopicParts[1] = (const char*)pMqttDownloaderThingName;
    pGetStreamTopicParts[3] = (const char*)pMqttDownloaderStreamName;

    topicLen = (uint16_t)stringBuilder(pGetStreamTopic,
        sizeof(pGetStreamTopic), pGetStreamTopicParts);

    printf("Get Stream topic is %s\n", pGetStreamTopic);

    assert((topicLen > 0U) && (topicLen < sizeof(pGetStreamTopic)));
    
    /* Initalizing the Subscribe Act status */
    // xDataTopicFilterContext.pcTopicFilter = pRxStreamTopic;
    // xDataTopicFilterContext.xSubAckStatus = MQTTSubAckFailure;
    
    //prvMQTTSubscribeWithRetries(pxMQTTContext, pRxStreamTopic);
    mqttSubscribe(pRxStreamTopic, topicLen);

    return 0;
}


uint8_t ucRequestDataBlock(uint16_t usFileId,
                            uint32_t ulBlockSize,
                            uint16_t usBlockOffset,
                            uint32_t ulNumberOfBlocksRequested)
{
    char getStreamRequest[GET_STREAM_REQUEST_BUFFER_SIZE];

    memset(getStreamRequest, '\0', GET_STREAM_REQUEST_BUFFER_SIZE);
     
    /*
     * Get stream request format
     * 
     *   "{ \"s\" : 1, \"f\": 1, \"l\": 256, \"o\": 0, \"n\": 1 }";
    */

    snprintf(getStreamRequest, GET_STREAM_REQUEST_BUFFER_SIZE,
                                "{"
                                    "\"s\": 1,"
                                    "\"f\": %u,"
                                    "\"l\": %u,"
                                    "\"o\": %u,"
                                    "\"n\": %u"
                                    
                                "}",
                                    usFileId,
                                    ulBlockSize,
                                    usBlockOffset,
                                    ulNumberOfBlocksRequested
                                );

    mqttPublish(pGetStreamTopic, strlen(pGetStreamTopic), (uint8_t *)getStreamRequest, strlen(getStreamRequest));

    return 0;
}

bool mqttStreams_handleIncomingMessage( char * topic,
                                        size_t topicLength,
                                        uint8_t * message,
                                        size_t messageLength )
{
    /* Process incoming Publish. */
    printf("MQTT streams handling incoming message \n");

    /* Verify the received publish is for the we have subscribed to. */
    if ((topicLength == strlen(pRxStreamTopic)) &&
        (0 == strncmp(pRxStreamTopic, topic, topicLength)))
    {
        printf("Incoming Publish Topic Length: %lu Name: %s matches subscribed topic.\r\n"
            "Incoming Publish Message length: %lu Message: %s\r\n",
            topicLength,
            topic,
            messageLength,
            (char *)message);
        
        JSONStatus_t result;
        char dataQuery[] = "p";
        size_t dataQueryLength = sizeof(dataQuery) - 1;
        char* dataValue;
        size_t dataValueLength;

        result = JSON_Search((char *)message, messageLength, dataQuery, dataQueryLength,
            &dataValue, &dataValueLength);
    
        if (result == JSONSuccess)
        {
            MqttFileDownloaderDataBlockInfo_t dataBlock;
            dataBlock.payload = (uint8_t *) dataValue;
            dataBlock.payloadLength = dataValueLength;
            //char save = dataValue[dataValueLength];
            
            //dataValue[dataValueLength] = '\0';
            
            printf("Found: %s -> %s\n", dataQuery, dataValue);
            otaDemo_handleMqttStreamsBlockArrived( &dataBlock );
            return true;
        }
    
    }
    else
    {
        printf("Incoming Publish Topic Name: %s does not match subscribed topic.\r\n",
            topic);
    }

    return false;
}


// void prvUpdateSubAckStatus(MQTTPacketInfo_t* pxPacketInfo)
// {
//     MQTTStatus_t xResult = MQTTSuccess;
//     uint8_t* pucPayload = NULL;
//     size_t ulSize = 0;

//     xResult = MQTT_GetSubAckStatusCodes(pxPacketInfo, &pucPayload, &ulSize);

//     assert(xResult == MQTTSuccess);

 
//     xDataTopicFilterContext.xSubAckStatus = pucPayload[0];

// }


// static MQTTStatus_t prvProcessLoopWithTimeout(MQTTContext_t* pMqttContext,
//     uint32_t ulTimeoutMs)
// {
//     uint32_t ulMqttProcessLoopTimeoutTime;
//     uint32_t ulCurrentTime;

//     MQTTStatus_t eMqttStatus = MQTTSuccess;

//     ulCurrentTime = pMqttContext->getTime();
//     ulMqttProcessLoopTimeoutTime = ulCurrentTime + ulTimeoutMs;

//     while ((ulCurrentTime < ulMqttProcessLoopTimeoutTime) &&
//         (eMqttStatus == MQTTSuccess || eMqttStatus == MQTTNeedMoreBytes))
//     {
//         eMqttStatus = MQTT_ProcessLoop(pMqttContext);
//         ulCurrentTime = pMqttContext->getTime();
//     }

//     if (eMqttStatus == MQTTNeedMoreBytes)
//     {
//         eMqttStatus = MQTTSuccess;
//     }

//     return eMqttStatus;
// }


// static bool prvMQTTSubscribeWithRetries(MQTTContext_t* pxMQTTContext, char* pTopicName)
// {
//     MQTTStatus_t xResult = MQTTSuccess;
//     uint8_t ucRetryCount = 0U;
//     MQTTSubscribeInfo_t xMQTTSubscription[mqttFileDownloaderSubscribeTOPIC_COUNT];
//     bool xIsSubscribeToTopic = false;

//     (void)memset((void*)&xMQTTSubscription, 0x00, sizeof(xMQTTSubscription));

//     /* Get a unique packet id. */
//     usDataTopicSubscribePacketIdentifier = MQTT_GetPacketId(pxMQTTContext);

//     /* Subcribe to the topic passed as input*/
//     xMQTTSubscription[0].qos = MQTTQoS1;
//     xMQTTSubscription[0].pTopicFilter = pTopicName;
//     xMQTTSubscription[0].topicFilterLength = (uint16_t)strlen(pTopicName);


//     do
//     {
//         printf("Attempt to subscribe to the MQTT topic %s.\r\n", pTopicName);
//         xResult = MQTT_Subscribe(pxMQTTContext,
//             xMQTTSubscription,
//             sizeof(xMQTTSubscription) / sizeof(MQTTSubscribeInfo_t),
//             usDataTopicSubscribePacketIdentifier);
//         assert(xResult == MQTTSuccess);

//         printf("SUBSCRIBE sent for topic %s to broker.\n\n", pTopicName);

//         /* Process incoming packet from the broker.*/
//         xResult = prvProcessLoopWithTimeout(pxMQTTContext, mqttFileDownloaderPROCESS_LOOP_TIMEOUT_MS);
//         assert(xResult == MQTTSuccess);

//         /* Reset the flag before checking suback responses. */
//         xIsSubscribeToTopic = false;

//         /* Check if recent subscription request has been accepted */
//         if (xDataTopicFilterContext.xSubAckStatus != MQTTSubAckFailure)
//         {
//             xIsSubscribeToTopic = true;
//             printf("Subscribed to the topic %s with maximum QoS %u.\r\n",
//                                 xDataTopicFilterContext.pcTopicFilter,
//                                 xDataTopicFilterContext.xSubAckStatus );
//             break;
//         }
//         ucRetryCount++;
    
//     } while ((xIsSubscribeToTopic == false) && (ucRetryCount < mqttFileDownloaderSubscribeRETRY_COUNT));

//     return xIsSubscribeToTopic;
// }

// void prvMQTTPublishToTopic(MQTTContext_t* pxMQTTContext, char* pTopicName, char* pMessage)
// {
//     MQTTStatus_t xResult;
//     MQTTPublishInfo_t xMQTTPublishInfo;

//     (void)memset((void*)&xMQTTPublishInfo, 0x00, sizeof(xMQTTPublishInfo));

//     xMQTTPublishInfo.qos = MQTTQoS1;
//     xMQTTPublishInfo.retain = false;
//     xMQTTPublishInfo.pTopicName = pTopicName;
//     xMQTTPublishInfo.topicNameLength = (uint16_t)strlen(pTopicName);
//     xMQTTPublishInfo.pPayload = pMessage;
//     xMQTTPublishInfo.payloadLength = strlen(pMessage);

//     /* Get a unique packet id. */
//     usGetDataPublishPacketIdentifier = MQTT_GetPacketId(pxMQTTContext);

//     /* Send PUBLISH packet */
//     xResult = MQTT_Publish(pxMQTTContext, &xMQTTPublishInfo, usGetDataPublishPacketIdentifier);

//     assert(xResult == MQTTSuccess);
// }