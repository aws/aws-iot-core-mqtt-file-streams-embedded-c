## v1.2.0 (March 2026)
- [#42](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/42) Remove formatting bot workflow
- [#39](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/39) Update ESP-IDF CI: pin tinycbor to a specific commit, fix incompatible-pointer-types warning in CBOR decoder by using an intermediate `int` buffer instead of direct casts to `int32_t *`, fix lcov coverage filtering, and update memory size statistics
- [#37](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/37) Update LTS 202406 information
- Fix broken coverity link in readme

## v1.1.0 (June 2024)
 - [#32](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/32) Make block size for file transfer configurable from 256 bytes to 128 KiloBytes.
 - [#23](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/23) Update API to return the fileID, blockID and blockSize.
 - [#22](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/22) Fix MISRA C 2012 violations.
 - [#20](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/pull/20) Move base64 decode table out of function to reduce function complexity.

## v1.0.0 (November 2023)

This is the first release of the AWS IoT MQTT File Streaming Embedded C Library in this
repository.
