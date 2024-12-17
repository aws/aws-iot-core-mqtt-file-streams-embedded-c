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
 * @file MQTTFileDownloader_json.h
 * @brief Function declarations and field declarations for
 * MQTTFileDownloader_json.c.
 */

#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

bool JSON_Encode_GetStreamRequestMessage(char * messageBuffer,
                                    size_t messageBufferSize,
                                    size_t * encodedMessageSize,
                                    uint16_t fileId,
                                    uint32_t blockSize,
                                    uint16_t blockOffset,
                                    uint32_t numberOfBlocksRequested,
                                    const uint8_t * blockBitmap,
                                    size_t blockBitmapSize);