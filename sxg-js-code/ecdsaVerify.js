var EC = require("elliptic").ec;
var { Buffer } = require("node:buffer");
var sha256 = require("js-sha256");

/** CBOR Encode from https://github.com/paroga/cbor-js */
var POW_2_24 = 5.960464477539063e-8,
  POW_2_32 = 4294967296,
  POW_2_53 = 9007199254740992;

function encode(value) {
  var data = new ArrayBuffer(256);
  var dataView = new DataView(data);
  var lastLength;
  var offset = 0;

  function prepareWrite(length) {
    var newByteLength = data.byteLength;
    var requiredLength = offset + length;
    while (newByteLength < requiredLength) newByteLength <<= 1;
    if (newByteLength !== data.byteLength) {
      var oldDataView = dataView;
      data = new ArrayBuffer(newByteLength);
      dataView = new DataView(data);
      var uint32count = (offset + 3) >> 2;
      for (var i = 0; i < uint32count; ++i)
        dataView.setUint32(i << 2, oldDataView.getUint32(i << 2));
    }

    lastLength = length;
    return dataView;
  }
  function commitWrite() {
    offset += lastLength;
  }
  function writeFloat64(value) {
    commitWrite(prepareWrite(8).setFloat64(offset, value));
  }
  function writeUint8(value) {
    commitWrite(prepareWrite(1).setUint8(offset, value));
  }
  function writeUint8Array(value) {
    var dataView = prepareWrite(value.length);
    console.log(value);
    for (var i = 0; i < value.length; ++i) {
      dataView.setUint8(offset + i, value[i]);
    }
    commitWrite();
  }
  function writeUint16(value) {
    commitWrite(prepareWrite(2).setUint16(offset, value));
  }
  function writeUint32(value) {
    commitWrite(prepareWrite(4).setUint32(offset, value));
  }
  function writeUint64(value) {
    var low = value % POW_2_32;
    var high = (value - low) / POW_2_32;
    var dataView = prepareWrite(8);
    dataView.setUint32(offset, high);
    dataView.setUint32(offset + 4, low);
    commitWrite();
  }
  function writeTypeAndLength(type, length) {
    if (length < 24) {
      writeUint8((type << 5) | length);
    } else if (length < 0x100) {
      writeUint8((type << 5) | 24);
      writeUint8(length);
    } else if (length < 0x10000) {
      writeUint8((type << 5) | 25);
      writeUint16(length);
    } else if (length < 0x100000000) {
      writeUint8((type << 5) | 26);
      writeUint32(length);
    } else {
      writeUint8((type << 5) | 27);
      writeUint64(length);
    }
  }

  function encodeItem(value) {
    var i;

    if (value === false) return writeUint8(0xf4);
    if (value === true) return writeUint8(0xf5);
    if (value === null) return writeUint8(0xf6);
    if (value === undefined) return writeUint8(0xf7);

    switch (typeof value) {
      case "number":
        if (Math.floor(value) === value) {
          if (0 <= value && value <= POW_2_53)
            return writeTypeAndLength(0, value);
          if (-POW_2_53 <= value && value < 0)
            return writeTypeAndLength(1, -(value + 1));
        }
        writeUint8(0xfb);
        return writeFloat64(value);

      case "string":
        var utf8data = [];
        for (i = 0; i < value.length; ++i) {
          var charCode = value.charCodeAt(i);
          if (charCode < 0x80) {
            utf8data.push(charCode);
          } else if (charCode < 0x800) {
            utf8data.push(0xc0 | (charCode >> 6));
            utf8data.push(0x80 | (charCode & 0x3f));
          } else if (charCode < 0xd800) {
            utf8data.push(0xe0 | (charCode >> 12));
            utf8data.push(0x80 | ((charCode >> 6) & 0x3f));
            utf8data.push(0x80 | (charCode & 0x3f));
          } else {
            charCode = (charCode & 0x3ff) << 10;
            charCode |= value.charCodeAt(++i) & 0x3ff;
            charCode += 0x10000;

            utf8data.push(0xf0 | (charCode >> 18));
            utf8data.push(0x80 | ((charCode >> 12) & 0x3f));
            utf8data.push(0x80 | ((charCode >> 6) & 0x3f));
            utf8data.push(0x80 | (charCode & 0x3f));
          }
        }

        writeTypeAndLength(3, utf8data.length);
        return writeUint8Array(utf8data);

      default:
        var length;
        if (Array.isArray(value)) {
          length = value.length;
          writeTypeAndLength(4, length);
          for (i = 0; i < length; ++i) encodeItem(value[i]);
        } else if (value instanceof Uint8Array) {
          writeTypeAndLength(2, value.length);
          writeUint8Array(value);
        } else {
          var keys = Object.keys(value);
          length = keys.length;
          writeTypeAndLength(5, length);
          for (i = 0; i < length; ++i) {
            var key = keys[i];
            console.log(key);
            encodeItem(key);
            encodeItem(value[key]);
          }
        }
    }
  }

  encodeItem(value);

  if ("slice" in data) return data.slice(0, offset);

  var ret = new ArrayBuffer(offset);
  var retView = new DataView(ret);
  for (var i = 0; i < offset; ++i) retView.setUint8(i, dataView.getUint8(i));
  return ret;
}

function decode(data, tagger, simpleValue) {
  var dataView = new DataView(data);
  var offset = 0;

  if (typeof tagger !== "function")
    tagger = function (value) {
      return value;
    };
  if (typeof simpleValue !== "function")
    simpleValue = function () {
      return undefined;
    };

  function commitRead(length, value) {
    offset += length;
    return value;
  }
  function readArrayBuffer(length) {
    return commitRead(length, new Uint8Array(data, offset, length));
  }
  function readFloat16() {
    var tempArrayBuffer = new ArrayBuffer(4);
    var tempDataView = new DataView(tempArrayBuffer);
    var value = readUint16();

    var sign = value & 0x8000;
    var exponent = value & 0x7c00;
    var fraction = value & 0x03ff;

    if (exponent === 0x7c00) exponent = 0xff << 10;
    else if (exponent !== 0) exponent += (127 - 15) << 10;
    else if (fraction !== 0) return (sign ? -1 : 1) * fraction * POW_2_24;

    tempDataView.setUint32(
      0,
      (sign << 16) | (exponent << 13) | (fraction << 13)
    );
    return tempDataView.getFloat32(0);
  }
  function readFloat32() {
    return commitRead(4, dataView.getFloat32(offset));
  }
  function readFloat64() {
    return commitRead(8, dataView.getFloat64(offset));
  }
  function readUint8() {
    return commitRead(1, dataView.getUint8(offset));
  }
  function readUint16() {
    return commitRead(2, dataView.getUint16(offset));
  }
  function readUint32() {
    return commitRead(4, dataView.getUint32(offset));
  }
  function readUint64() {
    return readUint32() * POW_2_32 + readUint32();
  }
  function readBreak() {
    if (dataView.getUint8(offset) !== 0xff) return false;
    offset += 1;
    return true;
  }
  function readLength(additionalInformation) {
    if (additionalInformation < 24) return additionalInformation;
    if (additionalInformation === 24) return readUint8();
    if (additionalInformation === 25) return readUint16();
    if (additionalInformation === 26) return readUint32();
    if (additionalInformation === 27) return readUint64();
    if (additionalInformation === 31) return -1;
    throw "Invalid length encoding";
  }
  function readIndefiniteStringLength(majorType) {
    var initialByte = readUint8();
    if (initialByte === 0xff) return -1;
    var length = readLength(initialByte & 0x1f);
    if (length < 0 || initialByte >> 5 !== majorType)
      throw "Invalid indefinite length element";
    return length;
  }

  function appendUtf16Data(utf16data, length) {
    for (var i = 0; i < length; ++i) {
      var value = readUint8();
      if (value & 0x80) {
        if (value < 0xe0) {
          value = ((value & 0x1f) << 6) | (readUint8() & 0x3f);
          length -= 1;
        } else if (value < 0xf0) {
          value =
            ((value & 0x0f) << 12) |
            ((readUint8() & 0x3f) << 6) |
            (readUint8() & 0x3f);
          length -= 2;
        } else {
          value =
            ((value & 0x0f) << 18) |
            ((readUint8() & 0x3f) << 12) |
            ((readUint8() & 0x3f) << 6) |
            (readUint8() & 0x3f);
          length -= 3;
        }
      }

      if (value < 0x10000) {
        utf16data.push(value);
      } else {
        value -= 0x10000;
        utf16data.push(0xd800 | (value >> 10));
        utf16data.push(0xdc00 | (value & 0x3ff));
      }
    }
  }

  function decodeItem() {
    var initialByte = readUint8();
    var majorType = initialByte >> 5;
    var additionalInformation = initialByte & 0x1f;
    var i;
    var length;

    if (majorType === 7) {
      switch (additionalInformation) {
        case 25:
          return readFloat16();
        case 26:
          return readFloat32();
        case 27:
          return readFloat64();
      }
    }

    length = readLength(additionalInformation);
    if (length < 0 && (majorType < 2 || 6 < majorType)) throw "Invalid length";

    switch (majorType) {
      case 0:
        return length;
      case 1:
        return -1 - length;
      case 2:
        if (length < 0) {
          var elements = [];
          var fullArrayLength = 0;
          while ((length = readIndefiniteStringLength(majorType)) >= 0) {
            fullArrayLength += length;
            elements.push(readArrayBuffer(length));
          }
          var fullArray = new Uint8Array(fullArrayLength);
          var fullArrayOffset = 0;
          for (i = 0; i < elements.length; ++i) {
            fullArray.set(elements[i], fullArrayOffset);
            fullArrayOffset += elements[i].length;
          }
          return fullArray;
        }
        return readArrayBuffer(length);
      case 3:
        var utf16data = [];
        if (length < 0) {
          while ((length = readIndefiniteStringLength(majorType)) >= 0)
            appendUtf16Data(utf16data, length);
        } else appendUtf16Data(utf16data, length);
        return String.fromCharCode.apply(null, utf16data);
      case 4:
        var retArray;
        if (length < 0) {
          retArray = [];
          while (!readBreak()) retArray.push(decodeItem());
        } else {
          retArray = new Array(length);
          for (i = 0; i < length; ++i) retArray[i] = decodeItem();
        }
        return retArray;
      case 5:
        var retObject = {};
        for (i = 0; i < length || (length < 0 && !readBreak()); ++i) {
          var key = decodeItem();
          retObject[key] = decodeItem();
        }
        return retObject;
      case 6:
        return tagger(decodeItem(), length);
      case 7:
        switch (length) {
          case 20:
            return false;
          case 21:
            return true;
          case 22:
            return null;
          case 23:
            return undefined;
          default:
            return simpleValue(length);
        }
    }
  }

  var ret = decodeItem();
  if (offset !== data.byteLength) throw "Remaining bytes";
  return ret;
}

function encodeBytesUint(n, size) {
  if (size < 7 && n > 1 << (size * 8)) {
    throw new Error("Value out of range");
  }

  var bytes = new Uint8Array(size);
  for (var i = 0; i < size; i++) {
    bytes[i] = (n >> ((size - i - 1) * 8)) & 0xff;
  }
  return bytes;
}

/** Defining P-256 curve */
var ec = new EC("p256");
var a = BigInt(
  "0xffffffff00000001000000000000000000000000fffffffffffffffffffffffc"
);
var b = BigInt(
  "0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b"
);
var p = BigInt(
  "0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff"
);

// data from sample certificate
let sgn =
  "30 44 02 20 3F B7 E8 CE 72 62 73 B2 A4 3C 10 8B 72 75 5E 96 CF DA 07 5F E4 1A 0C 67 80 2F B6 4A CD EB 0B EA 02 20 0B 86 0C FA EB 9D 2B B0 99 60 07 84 1D B2 6E 40 6C 11 56 7A 38 33 FE 56 AE A1 54 C2 C5 89 CB B0";

let pkey =
  "00 04 61 57 16 C8 8B 29 D4 CD 26 A7 12 70 9F B5 CD 5B 12 46 8C 65 71 63 FD 60 06 AA 3A 1B 6A 12 37 0A 42 F3 CC D3 BA 62 41 DC 74 32 89 B2 7A C9 E0 1D 9F 6D 04 04 BF AA 45 3D 93 DC 83 3E 25 B7 7B 1E";

// set up pkey
pkey = pkey.replace(/\s/g, "");
var pub = {
  x: pkey.slice(4, 68),
  y: pkey.slice(68),
};
var key = ec.keyFromPublic(pub, "hex");
var xbi = BigInt("0x" + pub.x);
var ybi = BigInt("0x" + pub.y);

// test point is actually on curve
console.log(((ybi * ybi) % p) - ((xbi * xbi * xbi + a * xbi + b) % p) === 0n);

/** Get signed message **/
// following code from https://github.com/WICG/webpackage/blob/30df64c8720e2c1889ddd54588b21256ed28a904/go/signedexchange/signer.go#L121
// taken from https://datatracker.ietf.org/doc/html/draft-yasskin-httpbis-origin-signed-exchanges-impl-03#section-3.5

// 1
var prefix = [];
for (var i = 0; i < 64; i++) {
  prefix.push(0x20);
}
let buf = Buffer.from(prefix);

// 2
buf = Buffer.concat([buf, Buffer.from("HTTP Exchange 1 b3", "ascii")]);

// 3
buf = Buffer.concat([buf, Buffer.from([0x00])]);

// 4
buf = Buffer.concat([buf, Buffer.from([32])]);
let certSha256 =
  "3F E4 4B 0B 5A E1 68 ED 9F A0 F2 77 F7 19 04 6E A9 33 15 4F 23 5B F6 24 78 E9 AE BE 28 CC CA DB"
    .split(/\s+/)
    .map((x) => parseInt(x, 16));
buf = Buffer.concat([buf, Buffer.from(certSha256)]);

// 5
const validityUrl = "https://signed-exchange-testing.dev/validity.msg";
const validityURlBuf = Buffer.from(validityUrl);
const validityUrlBufLen = Buffer.from(
  encodeBytesUint(Buffer.byteLength(validityUrl), 8)
);
buf = Buffer.concat([buf, validityUrlBufLen, validityURlBuf]);

// 6
const date = Math.floor(
  new Date("Thu, 06 Oct 2022 08:00:03 GMT").getTime() / 1000
);
buf = Buffer.concat([buf, Buffer.from(encodeBytesUint(date, 8))]);

// 7
const expires = Math.floor(
  new Date("Fri, 07 Oct 2022 08:00:03 GMT").getTime() / 1000
);
buf = Buffer.concat([buf, Buffer.from(encodeBytesUint(expires, 8))]);

// 8
const requestUrl = "https://signed-exchange-testing.dev/sxgs/valid.html";
const requestUrlBuf = Buffer.from(requestUrl);
const requestUrlBufLen = Buffer.from(
  encodeBytesUint(Buffer.byteLength(requestUrl), 8)
);
buf = Buffer.concat([buf, requestUrlBufLen, requestUrlBuf]);

// 9
let responseHeaders = {
  ":status": "200",
  "content-encoding": "mi-sha256-03",
  "content-type": "text/html; charset=utf-8",
  digest: "mi-sha256-03=+g9t4KB79Gt4iWA+SHo8bz9HIOgkR3PA2Nv9uLOr9JA=",
  "x-content-type-options": "nosniff",
};
const responseHeadersBuf = Buffer.from(encode(responseHeaders));
console.log(decode(encode(responseHeaders)));
const responseHeadersBufLen = Buffer.from(
  encodeBytesUint(Buffer.byteLength(responseHeadersBuf), 8)
);
buf = Buffer.concat([buf, responseHeadersBufLen, responseHeadersBuf]);

const finalMsg = sha256(buf);

console.log(key.verify(finalMsg, sgn));
