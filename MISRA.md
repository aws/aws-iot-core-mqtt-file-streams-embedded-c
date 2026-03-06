# MISRA Compliance

The jobs library files conform to the [MISRA C:2012](https://www.misra.org.uk)
guidelines, with some noted exceptions. Compliance is checked with Coverity static analysis.
The specific deviations, suppressed inline, are listed below.

Additionally, [MISRA configuration file](https://github.com/aws/aws-iot-core-mqtt-file-streams-embedded-c/blob/main/tools/coverity/misra.config) contains the project wide deviations.

### Suppressed with Coverity Comments
To find the violation references in the source files run grep on the source code
with ( Assuming rule 11.4 violation; with justification in point 2 ):
```
grep 'MISRA Ref 11.1.4' . -rI
```

#### Dir 4.6

_Ref 4.6.1_

- MISRA directive 4.6 prohibits use of types which do not have size information
  such as `int`. MQTT file streams library is dependent on the tiny cbor library to
  decode CBOR. The tiny CBOR API requires `int` as a parameter. All precautions are
  taken to handle the received data from the API carefully. The data is converted to
  `int32_t` after verifying that it will not overflow the bounds of 32-bits.

#### Rule 7.4

_Ref 7.4.1_

- MISRA Rule 7.4 prohibits modification of a string literal as that results in
  undefined behavior. This is a false positive as the rule allows casting a
  sting literal to const qualified pointer. In this case, the string literal is
  casted to a const unit8_t pointer so that it will not be modified.

#### Rule 8.9

_Ref 8.9.1_

- MISRA rule 8.9 says that a variable must be defined at block scope. In this
  case, the variable is a map which helps covert ASCII characters to base64
  characters. While this can be defined in the function, it makes the function
  too lengthy and complexity increases. Thus, this variable is defined as
  static and const at global scope.

#### Rule 14.3

_Ref 14.3.1_

- MISRA rule 14.3 prohibits presence of dead code. The file downloader library
  is designed to be compiled on many different platforms with different compilers.
  To that end, we need to guard against `int` being greater in size than what
  `int32_t` can hold. On the platform where `int` is 32-bits, these checks result in
  dead code.

#### Rule 21.6

_Ref 21.6.1_

- MISRA Rule 21.6 prohibits use of standard library functions as these
  functions might have implementation defined behavior. In this case, snprintf
  is used to populate a buffer to generate a data block request. The buffer is
  verified to be big enough to contain the populated buffer.
