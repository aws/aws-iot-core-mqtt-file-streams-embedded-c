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

#ifndef __CPROVER__
bool __CPROVER_assume( bool );
bool __CPROVER_r_ok( const void *, ... );
bool __CPROVER_rw_ok( const void *, ... );
#endif

/* Utils */
size_t nondet_sizet( void );
int nondet_int( void );

#define CBMC_MAX_OBJECT_SIZE ( PTRDIFF_MAX )
#define CBMC_MAX_BUFSIZE ( UNWIND_COUNT -1)
#define CBMC_STREAMNAME_MAX_LEN (UNWIND_COUNT -1)
#define CBMC_THINGNAME_MAX_LEN (UNWIND_COUNT -1)
#define CBMC_TOPIC_MAX_LEN (UNWIND_COUNT -1)
#define CBMC_MESSAGE_MAX_LEN (UNWIND_COUNT - 1)

static bool validateStr( char * str )
{
    return ( str != NULL );
}

static char * nondetStr( void )
{
    char * ret;
    ret = malloc( nondet_sizet() );
    __CPROVER_assume( validateStr( ret ) );
    return ret;
}

void proof_mqttDownloader_init( void )
{
    MqttFileDownloaderContext_t context = {0};
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

    ret = mqttDownloader_init(&context,
                              streamName,
                              streamNameLength,
                              thingName,
                              thingNameLength,
                              dataType);

    __CPROVER_assert(ret >= MQTTFileDownloaderSuccess && ret <= MQTTFileDownloaderDataDecodingFailed, 
                     "Return value is in range of MQTTFileDownloaderStatus_t" );
    
}

void proof_mqttDownloader_createGetDataBlockRequest( void )
{
    uint8_t dataType;
    uint16_t fileId;
    uint32_t blockSize;
    uint16_t blockOffset;
    uint32_t numberOfBlocksRequested;
    char * getStreamRequest; 
    uint32_t getStreamRequestLength;
    size_t ret;

    __CPROVER_assume(getStreamRequestLength >= 256);
    getStreamRequest = malloc(getStreamRequestLength);

    __CPROVER_assume(dataType == DATA_TYPE_JSON || dataType == DATA_TYPE_CBOR); 

    ret = mqttDownloader_createGetDataBlockRequest(dataType,
                                                   fileId,
                                                   blockSize,
                                                   blockOffset,
                                                   numberOfBlocksRequested,
                                                   getStreamRequest);

}

void proof_mqttDownloader_isDataBlockReceived( void )
{
    MqttFileDownloaderContext_t  context = {0};
    char * topic;
    size_t topicLength;
    bool ret;

    __CPROVER_assume(topicLength <= CBMC_TOPIC_MAX_LEN);
    topic = malloc(topicLength);

    ret = mqttDownloader_isDataBlockReceived(&context,
                                             topic,
                                             topicLength);

}

void proof_mqttDownloader_processReceivedDataBlock( void )
{
    MqttFileDownloaderContext_t  context = {0};
    uint8_t * message;
    size_t messageLength;
    uint8_t * data;
    size_t dataLength;
    bool ret;

    __CPROVER_assume(messageLength <= CBMC_TOPIC_MAX_LEN);
    message = malloc(messageLength);

    __CPROVER_assume(dataLength >= 256);
    data = malloc(dataLength);

    ret = mqttDownloader_processReceivedDataBlock(&context,
                                                  message,
                                                  messageLength,
                                                  data,
                                                  &dataLength);

}

void proof_mqttDownloader_base64_Decode( void )
{
    uint8_t * dest;
    const size_t destLen;
    size_t resultLen;
    const uint8_t * encodedData;
    const size_t encodedLen;
    Base64Status_t ret;

    __CPROVER_assume(destLen <= CBMC_MAX_BUFSIZE );
    dest = malloc(destLen);

    __CPROVER_assume(&resultLen != NULL);

    __CPROVER_assume(encodedLen <= CBMC_MAX_BUFSIZE );
    encodedData = malloc(encodedLen);

    ret = base64_Decode(dest,
                        destLen,
                        &resultLen,
                        encodedData,
                        encodedLen);
    
    __CPROVER_assert(ret >= Base64Success && ret <= Base64InvalidPaddingSymbol,
                    "Return value is in range of Base64Status_t.");

}

void proof_CBOR_Decode_GetStreamResponseMessage( void )
{
    const uint8_t * messageBuffer;
    size_t messageSize;
    int32_t fileId = nondet_int();
    int32_t blockId = nondet_int();
    int32_t blockSize = nondet_int();
    uint8_t * payload;
    size_t payloadSize;
    bool ret; 

    __CPROVER_assume(messageSize <= UNWIND_COUNT);
    messageBuffer = malloc(messageSize);

    __CPROVER_assume(payloadSize <= UNWIND_COUNT);
    payload = malloc(payloadSize);

    ret = CBOR_Decode_GetStreamResponseMessage(messageBuffer,
                                               messageSize,
                                               &fileId,
                                               &blockId,
                                               &blockSize,
                                               &payload,
                                               &payloadSize);
 
}

void proof_CBOR_Encode_GetStreamRequestMessage( void )
{
    uint8_t * messageBuffer;
    size_t messageBufferSize;;
    size_t encodedMessageSize = nondet_sizet();
    const char clientToken = nondetStr();
    uint32_t fileId;
    uint32_t blockSize;
    uint32_t blockOffset;
    const uint8_t blockBitmap = nondetStr();
    size_t blockBitmapSize = sizeof(blockBitmap);
    uint32_t numOfBlocksRequested;
    bool ret;

    __CPROVER_assume(messageBufferSize <= UINT32_MAX);
    messageBuffer = malloc(messageBufferSize);
    
    __CPROVER_assume( numOfBlocksRequested <= UNWIND_COUNT );

    ret = CBOR_Encode_GetStreamRequestMessage(messageBuffer,
                                              messageBufferSize,
                                              &encodedMessageSize,
                                              &clientToken,
                                              fileId,
                                              blockSize,
                                              blockOffset,
                                              &blockBitmap,
                                              blockBitmapSize,
                                              numOfBlocksRequested);
}

void proofs_fast( void )
{
    /* Functions in MQTTFileDownloader.c */
    proof_mqttDownloader_init();
    proof_mqttDownloader_createGetDataBlockRequest();
    proof_mqttDownloader_isDataBlockReceived();
    proof_mqttDownloader_processReceivedDataBlock();
    /* Functions in MQTTDownloader_base64.c */
    proof_mqttDownloader_base64_Decode();
    /* Functions in MQTTDownloader_cbor.c */
    proof_CBOR_Encode_GetStreamRequestMessage();
}

int main( )
{
    proofs_fast();
    proof_CBOR_Decode_GetStreamResponseMessage();
}
