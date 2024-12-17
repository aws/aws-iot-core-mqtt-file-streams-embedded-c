/*
 * AWS IoT Core MQTT File Streams Embedded C v1.1.0
 * Copyright (C) 2023 Amazon.com, Inc. and its affiliates. All Rights Reserved.
 * SPDX-License-Identifier: MIT
 *
 * Licensed under the MIT License. See the LICENSE accompanying this file
 * for the specific language governing permissions and limitations under
 * the License.
 */

/**
 * @file MQTTFileDownloader_json.c
 * @brief JSON encode/decode routines.
 */
/* Standard includes. */
#include <stdbool.h>

#include "MQTTFileDownloader_json.h"

#define OPTIONAL_BITMAP_BUFFER_SIZE 24583

bool JSON_Encode_GetStreamRequestMessage(char * messageBuffer,
                                    size_t messageBufferSize,
                                    size_t * encodedMessageSize,
                                    uint16_t fileId,
                                    uint32_t blockSize,
                                    uint16_t blockOffset,
                                    uint32_t numberOfBlocksRequested,
                                    const uint8_t * blockBitmap,
                                    size_t blockBitmapSize)
{
    bool jsonResult = true;
    /* Bitmap must be less than 12,288 bytes. */
    /* More details: https://docs.aws.amazon.com/iot/latest/developerguide/mqtt-based-file-delivery-in-devices.html#mqtt-based-file-delivery-get-getstream */
    char optionalKeys[OPTIONAL_BITMAP_BUFFER_SIZE] = {};

    if( ( messageBuffer == NULL ) || ( encodedMessageSize == NULL ) )
    {
        jsonResult = false;
    }

    if ( blockBitmap != NULL && blockBitmapSize != 0 )
    {
        snprintf(optionalKeys,
            OPTIONAL_BITMAP_BUFFER_SIZE,
            "\"b\": \"%.*s\"",
            ( int ) blockBitmapSize,
            blockBitmap );
    }

    if ( jsonResult == true )
    {
    /* MISRA Ref 21.6.1 [Use of snprintf] */
    /* More details at: https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c//blob/main/MISRA.md#rule-216 */
    /* coverity[misra_c_2012_rule_21_6_violation] */
    ( void ) snprintf( messageBuffer,
                        messageBufferSize,
                        "{"
                        "\"s\": 1,"
                        "\"f\": %u,"
                        "\"l\": %u,"
                        "\"o\": %u,"
                        "\"n\": %u",
                        "%s"
                        "}",
                        fileId,
                        blockSize,
                        blockOffset,
                        numberOfBlocksRequested,
                        optionalKeys);

    *encodedMessageSize = strnlen( messageBuffer,
                             messageBufferSize );
    }
}