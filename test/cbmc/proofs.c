#include <stdbool.h>
#include <stdio.h>
#include <assert.h>
#include <string.h>
#include <stdlib.h>

#include "MQTTFileDownloader_base64.h"
#include "MQTTFileDownloader_cbor.h"
#include "MQTTFileDownloader.h"
#include "core_json.h"


#ifndef UNWIND_COUNT
    #define UNWIND_COUNT 10
#endif

#define CBMC_MAX_OBJECT_SIZE ( PTRDIFF_MAX )
#define CBMC_MAX_BUFSIZE ( UNWIND_COUNT )
#define CBMC_STREAMNAME_MAX_LEN (UNWIND_COUNT -1)
#define CBMC_THINGNAME_MAX_LEN (UNWIND_COUNT -1)
#define CBMC_TOPIC_MAX_LEN (UNWIND_COUNT -1)

void proof_mqttDownloader_init( void )
{
    MqttFileDownloaderContext_t * context = {0};
    char * streamName;
    size_t streamNameLength;
    char * thingName;
    size_t thingNameLength;
    uint8_t dataType;
    uint8_t ret; 

    __CPROVER_assume( streamNameLength <= CBMC_STREAMNAME_MAX_LEN);
    streamName = malloc(streamNameLength);

    __CPROVER_assume(thingNameLength < CBMC_THINGNAME_MAX_LEN);
    thingName = malloc(thingNameLength); 

    __CPROVER_assume(dataType <= 255);

    ret = mqttDownloader_init(context,
                              streamName,
                              streamNameLength,
                              thingName,
                              thingNameLength,
                              dataType);
    
    
}

void proof_mqttDownloader_createGetDataBlockRequest( void )
{
    uint8_t dataType;
    uint16_t fileId;
    uint32_t blockSize;
    uint16_t blockOffset;
    uint32_t numberOfBlocksRequested;
    char * getStreamRequest[256] = {0}; 
    size_t ret;

    __CPROVER_assume(dataType == 0 || dataType == 1); 

    __CPROVER_assume(fileId != NULL );

    __CPROVER_assume(blockSize != NULL);

    __CPROVER_assume(blockOffset != NULL);

    __CPROVER_assume(numberOfBlocksRequested != NULL);

    ret = mqttDownloader_createGetDataBlockRequest(dataType,
                                                   fileId,
                                                   blockSize,
                                                   blockOffset,
                                                   numberOfBlocksRequested,
                                                   getStreamRequest);

}

void proof_mqttDownloader_isDataBlockReceived( void )
{
    MqttFileDownloaderContext_t * context = {0};
    char * topic;
    size_t topicLength;
    bool ret;

    //__CPROVER_assume(context->dataType != NULL);

    __CPROVER_assume(context->topicGetStream != NULL);

    //__CPROVER_assume(context->topicGetStreamLength != NULL);

    __CPROVER_assume(context->topicStreamData != NULL);

    __CPROVER_assume(context->topicStreamDataLength != NULL);

    __CPROVER_assume(topicLength <= CBMC_TOPIC_MAX_LEN);

    topic = malloc(topicLength);

    ret = mqttDownloader_isDataBlockReceived(context,
                                             topic,
                                             topicLength);

}

void proof_mqttDownloader_processReceivedDataBlock( void )
{
    MqttFileDownloaderContext_t * context = {0};
    uint8_t * message;
    size_t messageLength;
    uint8_t * data;
    size_t * dataLength;
    bool ret;

    __CPROVER_assume(context->dataType != NULL);

    __CPROVER_assume(context->topicGetStream != NULL);

    __CPROVER_assume(context->topicGetStreamLength != NULL);

    __CPROVER_assume(context->topicStreamData != NULL);

    __CPROVER_assume(context->topicStreamDataLength != NULL);

    __CPROVER_assume(messageLength <= CBMC_TOPIC_MAX_LEN);
    message = malloc(messageLength);

    __CPROVER_assume(dataLength <= CBMC_TOPIC_MAX_LEN);
    data = malloc(dataLength);

    ret = mqttDownloader_processReceivedDataBlock(context,
                                                  message,
                                                  messageLength,
                                                  data,
                                                  dataLength);

}

int main( )
{
    proof_mqttDownloader_init();
    proof_mqttDownloader_createGetDataBlockRequest();
    proof_mqttDownloader_isDataBlockReceived();
    proof_mqttDownloader_processReceivedDataBlock();
}