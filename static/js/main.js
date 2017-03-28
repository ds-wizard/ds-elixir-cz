"use strict";
// This object will hold all exports.
var Haste = {};
if(typeof window === 'undefined') window = global;

/* Constructor functions for small ADTs. */
function T0(t){this._=t;}
function T1(t,a){this._=t;this.a=a;}
function T2(t,a,b){this._=t;this.a=a;this.b=b;}
function T3(t,a,b,c){this._=t;this.a=a;this.b=b;this.c=c;}
function T4(t,a,b,c,d){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;}
function T5(t,a,b,c,d,e){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;}
function T6(t,a,b,c,d,e,f){this._=t;this.a=a;this.b=b;this.c=c;this.d=d;this.e=e;this.f=f;}

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// "Zero" object; used to avoid creating a whole bunch of new objects
// in the extremely common case of a nil-like data constructor.
var __Z = new T0(0);

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

// Indicates that a closure-creating tail loop isn't done.
var __continue = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof Function) {
            if(args.length === f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else if(f instanceof PAP) {
            if(args.length === f.arity) {
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                return new PAP(f.f, f.args.concat(args));
            } else {
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

function A1(f, x) {
    f = E(f);
    if(f instanceof Function) {
        return f.length === 1 ? f(x) : new PAP(f, [x]);
    } else if(f instanceof PAP) {
        return f.arity === 1 ? f.f.apply(null, f.args.concat([x]))
                             : new PAP(f.f, f.args.concat([x]));
    } else {
        return f;
    }
}

function A2(f, x, y) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 2:  return f(x, y);
        case 1:  return A1(B(f(x)), y);
        default: return new PAP(f, [x,y]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 2:  return f.f.apply(null, f.args.concat([x,y]));
        case 1:  return A1(B(f.f.apply(null, f.args.concat([x]))), y);
        default: return new PAP(f.f, f.args.concat([x,y]));
        }
    } else {
        return f;
    }
}

function A3(f, x, y, z) {
    f = E(f);
    if(f instanceof Function) {
        switch(f.length) {
        case 3:  return f(x, y, z);
        case 2:  return A1(B(f(x, y)), z);
        case 1:  return A2(B(f(x)), y, z);
        default: return new PAP(f, [x,y,z]);
        }
    } else if(f instanceof PAP) {
        switch(f.arity) {
        case 3:  return f.f.apply(null, f.args.concat([x,y,z]));
        case 2:  return A1(B(f.f.apply(null, f.args.concat([x,y]))), z);
        case 1:  return A2(B(f.f.apply(null, f.args.concat([x]))), y, z);
        default: return new PAP(f.f, f.args.concat([x,y,z]));
        }
    } else {
        return f;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        if(t.x === __updatable) {
            throw 'Infinite loop!';
        } else {
            return t.x;
        }
    } else {
        return t;
    }
}

/* Tail call chain counter. */
var C = 0, Cs = [];

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    Cs.push(C);
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        C = 0;
        f = fun();
    }
    C = Cs.pop();
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return {_:0, a:(a-a%b)/b, b:a%b};
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return {_:0, a:x & 0xffffffff, b:x > 0x7fffffff};
}

function subC(a, b) {
    var x = a-b;
    return {_:0, a:x & 0xffffffff, b:x < -2147483648};
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, __Z);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return {_:1,a:str.charCodeAt(i),b:new T(function() {
            return unAppCStr(str,chrs,i+1);
        })};
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str._ == 1; str = E(str.b)) {
        s += String.fromCharCode(E(str.a));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x.a;
    return x.b;
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

/* Convert a JS exception into a Haskell JSException */
function __hsException(e) {
  e = e.toString();
  var x = new Long(2904464383, 3929545892, true);
  var y = new Long(3027541338, 3270546716, true);
  var t = new T5(0, x, y
                  , new T5(0, x, y
                            , unCStr("haste-prim")
                            , unCStr("Haste.Prim.Foreign")
                            , unCStr("JSException")), __Z, __Z);
  var show = function(x) {return unCStr(E(x).a);}
  var dispEx = function(x) {return unCStr("JavaScript exception: " + E(x).a);}
  var showList = function(_, s) {return unAppCStr(e, s);}
  var showsPrec = function(_, _p, s) {return unAppCStr(e, s);}
  var showDict = new T3(0, showsPrec, show, showList);
  var self;
  var fromEx = function(_) {return new T1(1, self);}
  var dict = new T5(0, t, showDict, null /* toException */, fromEx, dispEx);
  self = new T2(0, dict, new T1(0, e));
  return self;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        if(typeof e._ === 'undefined') {
            e = __hsException(e);
        }
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Object) {
        return x._;
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(i.low) + popCnt(i.high);
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

function __clz(bits, x) {
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    } else {
        return bits - (1 + Math.floor(Math.log(x)/Math.LN2));
    }
}

// TODO: can probably be done much faster with arithmetic tricks like __clz
function __ctz(bits, x) {
    var y = 1;
    x &= (Math.pow(2, bits)-1);
    if(x === 0) {
        return bits;
    }
    for(var i = 0; i < bits; ++i) {
        if(y & x) {
            return i;
        } else {
            y <<= 1;
        }
    }
    return 0;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return __decodedZeroF;
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return {_:0, a:sign*man, b:exp};
}

var __decodedZero = {_:0,a:1,b:0,c:0,d:0};
var __decodedZeroF = {_:0,a:1,b:0};

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return __decodedZero;
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return {_:0, a:sign, b:manHigh, c:manLow, d:exp};
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs._) {
        strs = E(strs);
        arr.push(E(strs.a));
        strs = E(strs.b);
    }
    return arr.join(sep);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return __Z;
    }
    return {_:1,a:hs};
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return {_:0, a:jsRead(obj)};
    case 'string':
        return {_:1, a:obj};
    case 'boolean':
        return {_:2, a:obj}; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return {_:3, a:arr2lst_json(obj, 0)};
        } else if (obj == null) {
            return {_:5};
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = {_:1, a:{_:0, a:ks[i], b:toHS(obj[ks[i]])}, b:xs};
            }
            return {_:4, a:xs};
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1, a:toHS(arr[elem]), b:new T(function() {return arr2lst_json(arr,elem+1);}),c:true}
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

/* bn.js by Fedor Indutny, see doc/LICENSE.bn for license */
var __bn = {};
(function (module, exports) {
'use strict';

function BN(number, base, endian) {
  // May be `new BN(bn)` ?
  if (number !== null &&
      typeof number === 'object' &&
      Array.isArray(number.words)) {
    return number;
  }

  this.negative = 0;
  this.words = null;
  this.length = 0;

  if (base === 'le' || base === 'be') {
    endian = base;
    base = 10;
  }

  if (number !== null)
    this._init(number || 0, base || 10, endian || 'be');
}
if (typeof module === 'object')
  module.exports = BN;
else
  exports.BN = BN;

BN.BN = BN;
BN.wordSize = 26;

BN.max = function max(left, right) {
  if (left.cmp(right) > 0)
    return left;
  else
    return right;
};

BN.min = function min(left, right) {
  if (left.cmp(right) < 0)
    return left;
  else
    return right;
};

BN.prototype._init = function init(number, base, endian) {
  if (typeof number === 'number') {
    return this._initNumber(number, base, endian);
  } else if (typeof number === 'object') {
    return this._initArray(number, base, endian);
  }
  if (base === 'hex')
    base = 16;

  number = number.toString().replace(/\s+/g, '');
  var start = 0;
  if (number[0] === '-')
    start++;

  if (base === 16)
    this._parseHex(number, start);
  else
    this._parseBase(number, base, start);

  if (number[0] === '-')
    this.negative = 1;

  this.strip();

  if (endian !== 'le')
    return;

  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initNumber = function _initNumber(number, base, endian) {
  if (number < 0) {
    this.negative = 1;
    number = -number;
  }
  if (number < 0x4000000) {
    this.words = [ number & 0x3ffffff ];
    this.length = 1;
  } else if (number < 0x10000000000000) {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff
    ];
    this.length = 2;
  } else {
    this.words = [
      number & 0x3ffffff,
      (number / 0x4000000) & 0x3ffffff,
      1
    ];
    this.length = 3;
  }

  if (endian !== 'le')
    return;

  // Reverse the bytes
  this._initArray(this.toArray(), base, endian);
};

BN.prototype._initArray = function _initArray(number, base, endian) {
  if (number.length <= 0) {
    this.words = [ 0 ];
    this.length = 1;
    return this;
  }

  this.length = Math.ceil(number.length / 3);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  var off = 0;
  if (endian === 'be') {
    for (var i = number.length - 1, j = 0; i >= 0; i -= 3) {
      var w = number[i] | (number[i - 1] << 8) | (number[i - 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  } else if (endian === 'le') {
    for (var i = 0, j = 0; i < number.length; i += 3) {
      var w = number[i] | (number[i + 1] << 8) | (number[i + 2] << 16);
      this.words[j] |= (w << off) & 0x3ffffff;
      this.words[j + 1] = (w >>> (26 - off)) & 0x3ffffff;
      off += 24;
      if (off >= 26) {
        off -= 26;
        j++;
      }
    }
  }
  return this.strip();
};

function parseHex(str, start, end) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r <<= 4;

    // 'a' - 'f'
    if (c >= 49 && c <= 54)
      r |= c - 49 + 0xa;

    // 'A' - 'F'
    else if (c >= 17 && c <= 22)
      r |= c - 17 + 0xa;

    // '0' - '9'
    else
      r |= c & 0xf;
  }
  return r;
}

BN.prototype._parseHex = function _parseHex(number, start) {
  // Create possibly bigger array to ensure that it fits the number
  this.length = Math.ceil((number.length - start) / 6);
  this.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    this.words[i] = 0;

  // Scan 24-bit chunks and add them to the number
  var off = 0;
  for (var i = number.length - 6, j = 0; i >= start; i -= 6) {
    var w = parseHex(number, i, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
    off += 24;
    if (off >= 26) {
      off -= 26;
      j++;
    }
  }
  if (i + 6 !== start) {
    var w = parseHex(number, start, i + 6);
    this.words[j] |= (w << off) & 0x3ffffff;
    this.words[j + 1] |= w >>> (26 - off) & 0x3fffff;
  }
  this.strip();
};

function parseBase(str, start, end, mul) {
  var r = 0;
  var len = Math.min(str.length, end);
  for (var i = start; i < len; i++) {
    var c = str.charCodeAt(i) - 48;

    r *= mul;

    // 'a'
    if (c >= 49)
      r += c - 49 + 0xa;

    // 'A'
    else if (c >= 17)
      r += c - 17 + 0xa;

    // '0' - '9'
    else
      r += c;
  }
  return r;
}

BN.prototype._parseBase = function _parseBase(number, base, start) {
  // Initialize as zero
  this.words = [ 0 ];
  this.length = 1;

  // Find length of limb in base
  for (var limbLen = 0, limbPow = 1; limbPow <= 0x3ffffff; limbPow *= base)
    limbLen++;
  limbLen--;
  limbPow = (limbPow / base) | 0;

  var total = number.length - start;
  var mod = total % limbLen;
  var end = Math.min(total, total - mod) + start;

  var word = 0;
  for (var i = start; i < end; i += limbLen) {
    word = parseBase(number, i, i + limbLen, base);

    this.imuln(limbPow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }

  if (mod !== 0) {
    var pow = 1;
    var word = parseBase(number, i, number.length, base);

    for (var i = 0; i < mod; i++)
      pow *= base;
    this.imuln(pow);
    if (this.words[0] + word < 0x4000000)
      this.words[0] += word;
    else
      this._iaddn(word);
  }
};

BN.prototype.copy = function copy(dest) {
  dest.words = new Array(this.length);
  for (var i = 0; i < this.length; i++)
    dest.words[i] = this.words[i];
  dest.length = this.length;
  dest.negative = this.negative;
};

BN.prototype.clone = function clone() {
  var r = new BN(null);
  this.copy(r);
  return r;
};

// Remove leading `0` from `this`
BN.prototype.strip = function strip() {
  while (this.length > 1 && this.words[this.length - 1] === 0)
    this.length--;
  return this._normSign();
};

BN.prototype._normSign = function _normSign() {
  // -0 = 0
  if (this.length === 1 && this.words[0] === 0)
    this.negative = 0;
  return this;
};

var zeros = [
  '',
  '0',
  '00',
  '000',
  '0000',
  '00000',
  '000000',
  '0000000',
  '00000000',
  '000000000',
  '0000000000',
  '00000000000',
  '000000000000',
  '0000000000000',
  '00000000000000',
  '000000000000000',
  '0000000000000000',
  '00000000000000000',
  '000000000000000000',
  '0000000000000000000',
  '00000000000000000000',
  '000000000000000000000',
  '0000000000000000000000',
  '00000000000000000000000',
  '000000000000000000000000',
  '0000000000000000000000000'
];

var groupSizes = [
  0, 0,
  25, 16, 12, 11, 10, 9, 8,
  8, 7, 7, 7, 7, 6, 6,
  6, 6, 6, 6, 6, 5, 5,
  5, 5, 5, 5, 5, 5, 5,
  5, 5, 5, 5, 5, 5, 5
];

var groupBases = [
  0, 0,
  33554432, 43046721, 16777216, 48828125, 60466176, 40353607, 16777216,
  43046721, 10000000, 19487171, 35831808, 62748517, 7529536, 11390625,
  16777216, 24137569, 34012224, 47045881, 64000000, 4084101, 5153632,
  6436343, 7962624, 9765625, 11881376, 14348907, 17210368, 20511149,
  24300000, 28629151, 33554432, 39135393, 45435424, 52521875, 60466176
];

BN.prototype.toString = function toString(base, padding) {
  base = base || 10;
  var padding = padding | 0 || 1;
  if (base === 16 || base === 'hex') {
    var out = '';
    var off = 0;
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var w = this.words[i];
      var word = (((w << off) | carry) & 0xffffff).toString(16);
      carry = (w >>> (24 - off)) & 0xffffff;
      if (carry !== 0 || i !== this.length - 1)
        out = zeros[6 - word.length] + word + out;
      else
        out = word + out;
      off += 2;
      if (off >= 26) {
        off -= 26;
        i--;
      }
    }
    if (carry !== 0)
      out = carry.toString(16) + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else if (base === (base | 0) && base >= 2 && base <= 36) {
    var groupSize = groupSizes[base];
    var groupBase = groupBases[base];
    var out = '';
    var c = this.clone();
    c.negative = 0;
    while (c.cmpn(0) !== 0) {
      var r = c.modn(groupBase).toString(base);
      c = c.idivn(groupBase);

      if (c.cmpn(0) !== 0)
        out = zeros[groupSize - r.length] + r + out;
      else
        out = r + out;
    }
    if (this.cmpn(0) === 0)
      out = '0' + out;
    while (out.length % padding !== 0)
      out = '0' + out;
    if (this.negative !== 0)
      out = '-' + out;
    return out;
  } else {
    throw 'Base should be between 2 and 36';
  }
};

BN.prototype.toJSON = function toJSON() {
  return this.toString(16);
};

BN.prototype.toArray = function toArray(endian, length) {
  this.strip();
  var littleEndian = endian === 'le';
  var res = new Array(this.byteLength());
  res[0] = 0;

  var q = this.clone();
  if (!littleEndian) {
    // Assume big-endian
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[res.length - i - 1] = b;
    }
  } else {
    for (var i = 0; q.cmpn(0) !== 0; i++) {
      var b = q.andln(0xff);
      q.iushrn(8);

      res[i] = b;
    }
  }

  if (length) {
    while (res.length < length) {
      if (littleEndian)
        res.push(0);
      else
        res.unshift(0);
    }
  }

  return res;
};

if (Math.clz32) {
  BN.prototype._countBits = function _countBits(w) {
    return 32 - Math.clz32(w);
  };
} else {
  BN.prototype._countBits = function _countBits(w) {
    var t = w;
    var r = 0;
    if (t >= 0x1000) {
      r += 13;
      t >>>= 13;
    }
    if (t >= 0x40) {
      r += 7;
      t >>>= 7;
    }
    if (t >= 0x8) {
      r += 4;
      t >>>= 4;
    }
    if (t >= 0x02) {
      r += 2;
      t >>>= 2;
    }
    return r + t;
  };
}

// Return number of used bits in a BN
BN.prototype.bitLength = function bitLength() {
  var hi = 0;
  var w = this.words[this.length - 1];
  var hi = this._countBits(w);
  return (this.length - 1) * 26 + hi;
};

BN.prototype.byteLength = function byteLength() {
  return Math.ceil(this.bitLength() / 8);
};

// Return negative clone of `this`
BN.prototype.neg = function neg() {
  if (this.cmpn(0) === 0)
    return this.clone();

  var r = this.clone();
  r.negative = this.negative ^ 1;
  return r;
};

BN.prototype.ineg = function ineg() {
  this.negative ^= 1;
  return this;
};

// Or `num` with `this` in-place
BN.prototype.iuor = function iuor(num) {
  while (this.length < num.length)
    this.words[this.length++] = 0;

  for (var i = 0; i < num.length; i++)
    this.words[i] = this.words[i] | num.words[i];

  return this.strip();
};

BN.prototype.ior = function ior(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuor(num);
};


// Or `num` with `this`
BN.prototype.or = function or(num) {
  if (this.length > num.length)
    return this.clone().ior(num);
  else
    return num.clone().ior(this);
};

BN.prototype.uor = function uor(num) {
  if (this.length > num.length)
    return this.clone().iuor(num);
  else
    return num.clone().iuor(this);
};


// And `num` with `this` in-place
BN.prototype.iuand = function iuand(num) {
  // b = min-length(num, this)
  var b;
  if (this.length > num.length)
    b = num;
  else
    b = this;

  for (var i = 0; i < b.length; i++)
    this.words[i] = this.words[i] & num.words[i];

  this.length = b.length;

  return this.strip();
};

BN.prototype.iand = function iand(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuand(num);
};


// And `num` with `this`
BN.prototype.and = function and(num) {
  if (this.length > num.length)
    return this.clone().iand(num);
  else
    return num.clone().iand(this);
};

BN.prototype.uand = function uand(num) {
  if (this.length > num.length)
    return this.clone().iuand(num);
  else
    return num.clone().iuand(this);
};


// Xor `num` with `this` in-place
BN.prototype.iuxor = function iuxor(num) {
  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  for (var i = 0; i < b.length; i++)
    this.words[i] = a.words[i] ^ b.words[i];

  if (this !== a)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];

  this.length = a.length;

  return this.strip();
};

BN.prototype.ixor = function ixor(num) {
  //assert((this.negative | num.negative) === 0);
  return this.iuxor(num);
};


// Xor `num` with `this`
BN.prototype.xor = function xor(num) {
  if (this.length > num.length)
    return this.clone().ixor(num);
  else
    return num.clone().ixor(this);
};

BN.prototype.uxor = function uxor(num) {
  if (this.length > num.length)
    return this.clone().iuxor(num);
  else
    return num.clone().iuxor(this);
};


// Add `num` to `this` in-place
BN.prototype.iadd = function iadd(num) {
  // negative + positive
  if (this.negative !== 0 && num.negative === 0) {
    this.negative = 0;
    var r = this.isub(num);
    this.negative ^= 1;
    return this._normSign();

  // positive + negative
  } else if (this.negative === 0 && num.negative !== 0) {
    num.negative = 0;
    var r = this.isub(num);
    num.negative = 1;
    return r._normSign();
  }

  // a.length > b.length
  var a;
  var b;
  if (this.length > num.length) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) + (b.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    this.words[i] = r & 0x3ffffff;
    carry = r >>> 26;
  }

  this.length = a.length;
  if (carry !== 0) {
    this.words[this.length] = carry;
    this.length++;
  // Copy the rest of the words
  } else if (a !== this) {
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  }

  return this;
};

// Add `num` to `this`
BN.prototype.add = function add(num) {
  if (num.negative !== 0 && this.negative === 0) {
    num.negative = 0;
    var res = this.sub(num);
    num.negative ^= 1;
    return res;
  } else if (num.negative === 0 && this.negative !== 0) {
    this.negative = 0;
    var res = num.sub(this);
    this.negative = 1;
    return res;
  }

  if (this.length > num.length)
    return this.clone().iadd(num);
  else
    return num.clone().iadd(this);
};

// Subtract `num` from `this` in-place
BN.prototype.isub = function isub(num) {
  // this - (-num) = this + num
  if (num.negative !== 0) {
    num.negative = 0;
    var r = this.iadd(num);
    num.negative = 1;
    return r._normSign();

  // -this - num = -(this + num)
  } else if (this.negative !== 0) {
    this.negative = 0;
    this.iadd(num);
    this.negative = 1;
    return this._normSign();
  }

  // At this point both numbers are positive
  var cmp = this.cmp(num);

  // Optimization - zeroify
  if (cmp === 0) {
    this.negative = 0;
    this.length = 1;
    this.words[0] = 0;
    return this;
  }

  // a > b
  var a;
  var b;
  if (cmp > 0) {
    a = this;
    b = num;
  } else {
    a = num;
    b = this;
  }

  var carry = 0;
  for (var i = 0; i < b.length; i++) {
    var r = (a.words[i] | 0) - (b.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }
  for (; carry !== 0 && i < a.length; i++) {
    var r = (a.words[i] | 0) + carry;
    carry = r >> 26;
    this.words[i] = r & 0x3ffffff;
  }

  // Copy rest of the words
  if (carry === 0 && i < a.length && a !== this)
    for (; i < a.length; i++)
      this.words[i] = a.words[i];
  this.length = Math.max(this.length, i);

  if (a !== this)
    this.negative = 1;

  return this.strip();
};

// Subtract `num` from `this`
BN.prototype.sub = function sub(num) {
  return this.clone().isub(num);
};

function smallMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  var len = (self.length + num.length) | 0;
  out.length = len;
  len = (len - 1) | 0;

  // Peel one iteration (compiler can't do it, because of code complexity)
  var a = self.words[0] | 0;
  var b = num.words[0] | 0;
  var r = a * b;

  var lo = r & 0x3ffffff;
  var carry = (r / 0x4000000) | 0;
  out.words[0] = lo;

  for (var k = 1; k < len; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = carry >>> 26;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = (k - j) | 0;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;
    }
    out.words[k] = rword | 0;
    carry = ncarry | 0;
  }
  if (carry !== 0) {
    out.words[k] = carry | 0;
  } else {
    out.length--;
  }

  return out.strip();
}

function bigMulTo(self, num, out) {
  out.negative = num.negative ^ self.negative;
  out.length = self.length + num.length;

  var carry = 0;
  var hncarry = 0;
  for (var k = 0; k < out.length - 1; k++) {
    // Sum all words with the same `i + j = k` and accumulate `ncarry`,
    // note that ncarry could be >= 0x3ffffff
    var ncarry = hncarry;
    hncarry = 0;
    var rword = carry & 0x3ffffff;
    var maxJ = Math.min(k, num.length - 1);
    for (var j = Math.max(0, k - self.length + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = self.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      ncarry = (ncarry + ((r / 0x4000000) | 0)) | 0;
      lo = (lo + rword) | 0;
      rword = lo & 0x3ffffff;
      ncarry = (ncarry + (lo >>> 26)) | 0;

      hncarry += ncarry >>> 26;
      ncarry &= 0x3ffffff;
    }
    out.words[k] = rword;
    carry = ncarry;
    ncarry = hncarry;
  }
  if (carry !== 0) {
    out.words[k] = carry;
  } else {
    out.length--;
  }

  return out.strip();
}

BN.prototype.mulTo = function mulTo(num, out) {
  var res;
  if (this.length + num.length < 63)
    res = smallMulTo(this, num, out);
  else
    res = bigMulTo(this, num, out);
  return res;
};

// Multiply `this` by `num`
BN.prototype.mul = function mul(num) {
  var out = new BN(null);
  out.words = new Array(this.length + num.length);
  return this.mulTo(num, out);
};

// In-place Multiplication
BN.prototype.imul = function imul(num) {
  if (this.cmpn(0) === 0 || num.cmpn(0) === 0) {
    this.words[0] = 0;
    this.length = 1;
    return this;
  }

  var tlen = this.length;
  var nlen = num.length;

  this.negative = num.negative ^ this.negative;
  this.length = this.length + num.length;
  this.words[this.length - 1] = 0;

  for (var k = this.length - 2; k >= 0; k--) {
    // Sum all words with the same `i + j = k` and accumulate `carry`,
    // note that carry could be >= 0x3ffffff
    var carry = 0;
    var rword = 0;
    var maxJ = Math.min(k, nlen - 1);
    for (var j = Math.max(0, k - tlen + 1); j <= maxJ; j++) {
      var i = k - j;
      var a = this.words[i] | 0;
      var b = num.words[j] | 0;
      var r = a * b;

      var lo = r & 0x3ffffff;
      carry += (r / 0x4000000) | 0;
      lo += rword;
      rword = lo & 0x3ffffff;
      carry += lo >>> 26;
    }
    this.words[k] = rword;
    this.words[k + 1] += carry;
    carry = 0;
  }

  // Propagate overflows
  var carry = 0;
  for (var i = 1; i < this.length; i++) {
    var w = (this.words[i] | 0) + carry;
    this.words[i] = w & 0x3ffffff;
    carry = w >>> 26;
  }

  return this.strip();
};

BN.prototype.imuln = function imuln(num) {
  // Carry
  var carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = (this.words[i] | 0) * num;
    var lo = (w & 0x3ffffff) + (carry & 0x3ffffff);
    carry >>= 26;
    carry += (w / 0x4000000) | 0;
    // NOTE: lo is 27bit maximum
    carry += lo >>> 26;
    this.words[i] = lo & 0x3ffffff;
  }

  if (carry !== 0) {
    this.words[i] = carry;
    this.length++;
  }

  return this;
};

BN.prototype.muln = function muln(num) {
  return this.clone().imuln(num);
};

// `this` * `this`
BN.prototype.sqr = function sqr() {
  return this.mul(this);
};

// `this` * `this` in-place
BN.prototype.isqr = function isqr() {
  return this.mul(this);
};

// Shift-left in-place
BN.prototype.iushln = function iushln(bits) {
  var r = bits % 26;
  var s = (bits - r) / 26;
  var carryMask = (0x3ffffff >>> (26 - r)) << (26 - r);

  if (r !== 0) {
    var carry = 0;
    for (var i = 0; i < this.length; i++) {
      var newCarry = this.words[i] & carryMask;
      var c = ((this.words[i] | 0) - newCarry) << r;
      this.words[i] = c | carry;
      carry = newCarry >>> (26 - r);
    }
    if (carry) {
      this.words[i] = carry;
      this.length++;
    }
  }

  if (s !== 0) {
    for (var i = this.length - 1; i >= 0; i--)
      this.words[i + s] = this.words[i];
    for (var i = 0; i < s; i++)
      this.words[i] = 0;
    this.length += s;
  }

  return this.strip();
};

BN.prototype.ishln = function ishln(bits) {
  return this.iushln(bits);
};

// Shift-right in-place
BN.prototype.iushrn = function iushrn(bits, hint, extended) {
  var h;
  if (hint)
    h = (hint - (hint % 26)) / 26;
  else
    h = 0;

  var r = bits % 26;
  var s = Math.min((bits - r) / 26, this.length);
  var mask = 0x3ffffff ^ ((0x3ffffff >>> r) << r);
  var maskedWords = extended;

  h -= s;
  h = Math.max(0, h);

  // Extended mode, copy masked part
  if (maskedWords) {
    for (var i = 0; i < s; i++)
      maskedWords.words[i] = this.words[i];
    maskedWords.length = s;
  }

  if (s === 0) {
    // No-op, we should not move anything at all
  } else if (this.length > s) {
    this.length -= s;
    for (var i = 0; i < this.length; i++)
      this.words[i] = this.words[i + s];
  } else {
    this.words[0] = 0;
    this.length = 1;
  }

  var carry = 0;
  for (var i = this.length - 1; i >= 0 && (carry !== 0 || i >= h); i--) {
    var word = this.words[i] | 0;
    this.words[i] = (carry << (26 - r)) | (word >>> r);
    carry = word & mask;
  }

  // Push carried bits as a mask
  if (maskedWords && carry !== 0)
    maskedWords.words[maskedWords.length++] = carry;

  if (this.length === 0) {
    this.words[0] = 0;
    this.length = 1;
  }

  this.strip();

  return this;
};

BN.prototype.ishrn = function ishrn(bits, hint, extended) {
  return this.iushrn(bits, hint, extended);
};

// Shift-left
BN.prototype.shln = function shln(bits) {
  var x = this.clone();
  var neg = x.negative;
  x.negative = false;
  x.ishln(bits);
  x.negative = neg;
  return x;
};

BN.prototype.ushln = function ushln(bits) {
  return this.clone().iushln(bits);
};

// Shift-right
BN.prototype.shrn = function shrn(bits) {
  var x = this.clone();
  if(x.negative) {
      x.negative = false;
      x.ishrn(bits);
      x.negative = true;
      return x.isubn(1);
  } else {
      return x.ishrn(bits);
  }
};

BN.prototype.ushrn = function ushrn(bits) {
  return this.clone().iushrn(bits);
};

// Test if n bit is set
BN.prototype.testn = function testn(bit) {
  var r = bit % 26;
  var s = (bit - r) / 26;
  var q = 1 << r;

  // Fast case: bit is much higher than all existing words
  if (this.length <= s) {
    return false;
  }

  // Check bit and return
  var w = this.words[s];

  return !!(w & q);
};

// Add plain number `num` to `this`
BN.prototype.iaddn = function iaddn(num) {
  if (num < 0)
    return this.isubn(-num);

  // Possible sign change
  if (this.negative !== 0) {
    if (this.length === 1 && (this.words[0] | 0) < num) {
      this.words[0] = num - (this.words[0] | 0);
      this.negative = 0;
      return this;
    }

    this.negative = 0;
    this.isubn(num);
    this.negative = 1;
    return this;
  }

  // Add without checks
  return this._iaddn(num);
};

BN.prototype._iaddn = function _iaddn(num) {
  this.words[0] += num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] >= 0x4000000; i++) {
    this.words[i] -= 0x4000000;
    if (i === this.length - 1)
      this.words[i + 1] = 1;
    else
      this.words[i + 1]++;
  }
  this.length = Math.max(this.length, i + 1);

  return this;
};

// Subtract plain number `num` from `this`
BN.prototype.isubn = function isubn(num) {
  if (num < 0)
    return this.iaddn(-num);

  if (this.negative !== 0) {
    this.negative = 0;
    this.iaddn(num);
    this.negative = 1;
    return this;
  }

  this.words[0] -= num;

  // Carry
  for (var i = 0; i < this.length && this.words[i] < 0; i++) {
    this.words[i] += 0x4000000;
    this.words[i + 1] -= 1;
  }

  return this.strip();
};

BN.prototype.addn = function addn(num) {
  return this.clone().iaddn(num);
};

BN.prototype.subn = function subn(num) {
  return this.clone().isubn(num);
};

BN.prototype.iabs = function iabs() {
  this.negative = 0;

  return this;
};

BN.prototype.abs = function abs() {
  return this.clone().iabs();
};

BN.prototype._ishlnsubmul = function _ishlnsubmul(num, mul, shift) {
  // Bigger storage is needed
  var len = num.length + shift;
  var i;
  if (this.words.length < len) {
    var t = new Array(len);
    for (var i = 0; i < this.length; i++)
      t[i] = this.words[i];
    this.words = t;
  } else {
    i = this.length;
  }

  // Zeroify rest
  this.length = Math.max(this.length, len);
  for (; i < this.length; i++)
    this.words[i] = 0;

  var carry = 0;
  for (var i = 0; i < num.length; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    var right = (num.words[i] | 0) * mul;
    w -= right & 0x3ffffff;
    carry = (w >> 26) - ((right / 0x4000000) | 0);
    this.words[i + shift] = w & 0x3ffffff;
  }
  for (; i < this.length - shift; i++) {
    var w = (this.words[i + shift] | 0) + carry;
    carry = w >> 26;
    this.words[i + shift] = w & 0x3ffffff;
  }

  if (carry === 0)
    return this.strip();

  carry = 0;
  for (var i = 0; i < this.length; i++) {
    var w = -(this.words[i] | 0) + carry;
    carry = w >> 26;
    this.words[i] = w & 0x3ffffff;
  }
  this.negative = 1;

  return this.strip();
};

BN.prototype._wordDiv = function _wordDiv(num, mode) {
  var shift = this.length - num.length;

  var a = this.clone();
  var b = num;

  // Normalize
  var bhi = b.words[b.length - 1] | 0;
  var bhiBits = this._countBits(bhi);
  shift = 26 - bhiBits;
  if (shift !== 0) {
    b = b.ushln(shift);
    a.iushln(shift);
    bhi = b.words[b.length - 1] | 0;
  }

  // Initialize quotient
  var m = a.length - b.length;
  var q;

  if (mode !== 'mod') {
    q = new BN(null);
    q.length = m + 1;
    q.words = new Array(q.length);
    for (var i = 0; i < q.length; i++)
      q.words[i] = 0;
  }

  var diff = a.clone()._ishlnsubmul(b, 1, m);
  if (diff.negative === 0) {
    a = diff;
    if (q)
      q.words[m] = 1;
  }

  for (var j = m - 1; j >= 0; j--) {
    var qj = (a.words[b.length + j] | 0) * 0x4000000 +
             (a.words[b.length + j - 1] | 0);

    // NOTE: (qj / bhi) is (0x3ffffff * 0x4000000 + 0x3ffffff) / 0x2000000 max
    // (0x7ffffff)
    qj = Math.min((qj / bhi) | 0, 0x3ffffff);

    a._ishlnsubmul(b, qj, j);
    while (a.negative !== 0) {
      qj--;
      a.negative = 0;
      a._ishlnsubmul(b, 1, j);
      if (a.cmpn(0) !== 0)
        a.negative ^= 1;
    }
    if (q)
      q.words[j] = qj;
  }
  if (q)
    q.strip();
  a.strip();

  // Denormalize
  if (mode !== 'div' && shift !== 0)
    a.iushrn(shift);
  return { div: q ? q : null, mod: a };
};

BN.prototype.divmod = function divmod(num, mode, positive) {
  if (this.negative !== 0 && num.negative === 0) {
    var res = this.neg().divmod(num, mode);
    var div;
    var mod;
    if (mode !== 'mod')
      div = res.div.neg();
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.add(num);
    }
    return {
      div: div,
      mod: mod
    };
  } else if (this.negative === 0 && num.negative !== 0) {
    var res = this.divmod(num.neg(), mode);
    var div;
    if (mode !== 'mod')
      div = res.div.neg();
    return { div: div, mod: res.mod };
  } else if ((this.negative & num.negative) !== 0) {
    var res = this.neg().divmod(num.neg(), mode);
    var mod;
    if (mode !== 'div') {
      mod = res.mod.neg();
      if (positive && mod.neg)
        mod = mod.isub(num);
    }
    return {
      div: res.div,
      mod: mod
    };
  }

  // Both numbers are positive at this point

  // Strip both numbers to approximate shift value
  if (num.length > this.length || this.cmp(num) < 0)
    return { div: new BN(0), mod: this };

  // Very short reduction
  if (num.length === 1) {
    if (mode === 'div')
      return { div: this.divn(num.words[0]), mod: null };
    else if (mode === 'mod')
      return { div: null, mod: new BN(this.modn(num.words[0])) };
    return {
      div: this.divn(num.words[0]),
      mod: new BN(this.modn(num.words[0]))
    };
  }

  return this._wordDiv(num, mode);
};

// Find `this` / `num`
BN.prototype.div = function div(num) {
  return this.divmod(num, 'div', false).div;
};

// Find `this` % `num`
BN.prototype.mod = function mod(num) {
  return this.divmod(num, 'mod', false).mod;
};

BN.prototype.umod = function umod(num) {
  return this.divmod(num, 'mod', true).mod;
};

// Find Round(`this` / `num`)
BN.prototype.divRound = function divRound(num) {
  var dm = this.divmod(num);

  // Fast case - exact division
  if (dm.mod.cmpn(0) === 0)
    return dm.div;

  var mod = dm.div.negative !== 0 ? dm.mod.isub(num) : dm.mod;

  var half = num.ushrn(1);
  var r2 = num.andln(1);
  var cmp = mod.cmp(half);

  // Round down
  if (cmp < 0 || r2 === 1 && cmp === 0)
    return dm.div;

  // Round up
  return dm.div.negative !== 0 ? dm.div.isubn(1) : dm.div.iaddn(1);
};

BN.prototype.modn = function modn(num) {
  var p = (1 << 26) % num;

  var acc = 0;
  for (var i = this.length - 1; i >= 0; i--)
    acc = (p * acc + (this.words[i] | 0)) % num;

  return acc;
};

// In-place division by number
BN.prototype.idivn = function idivn(num) {
  var carry = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var w = (this.words[i] | 0) + carry * 0x4000000;
    this.words[i] = (w / num) | 0;
    carry = w % num;
  }

  return this.strip();
};

BN.prototype.divn = function divn(num) {
  return this.clone().idivn(num);
};

BN.prototype.isEven = function isEven() {
  return (this.words[0] & 1) === 0;
};

BN.prototype.isOdd = function isOdd() {
  return (this.words[0] & 1) === 1;
};

// And first word and num
BN.prototype.andln = function andln(num) {
  return this.words[0] & num;
};

BN.prototype.cmpn = function cmpn(num) {
  var negative = num < 0;
  if (negative)
    num = -num;

  if (this.negative !== 0 && !negative)
    return -1;
  else if (this.negative === 0 && negative)
    return 1;

  num &= 0x3ffffff;
  this.strip();

  var res;
  if (this.length > 1) {
    res = 1;
  } else {
    var w = this.words[0] | 0;
    res = w === num ? 0 : w < num ? -1 : 1;
  }
  if (this.negative !== 0)
    res = -res;
  return res;
};

// Compare two numbers and return:
// 1 - if `this` > `num`
// 0 - if `this` == `num`
// -1 - if `this` < `num`
BN.prototype.cmp = function cmp(num) {
  if (this.negative !== 0 && num.negative === 0)
    return -1;
  else if (this.negative === 0 && num.negative !== 0)
    return 1;

  var res = this.ucmp(num);
  if (this.negative !== 0)
    return -res;
  else
    return res;
};

// Unsigned comparison
BN.prototype.ucmp = function ucmp(num) {
  // At this point both numbers have the same sign
  if (this.length > num.length)
    return 1;
  else if (this.length < num.length)
    return -1;

  var res = 0;
  for (var i = this.length - 1; i >= 0; i--) {
    var a = this.words[i] | 0;
    var b = num.words[i] | 0;

    if (a === b)
      continue;
    if (a < b)
      res = -1;
    else if (a > b)
      res = 1;
    break;
  }
  return res;
};
})(undefined, __bn);

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return {_:0, a:0, b:undefined};
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return {_:0, a:1, b:val};
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

// TODO: inefficient compared to real fromInt?
__bn.Z = new __bn.BN(0);
__bn.ONE = new __bn.BN(1);
__bn.MOD32 = new __bn.BN(0x100000000); // 2^32
var I_fromNumber = function(x) {return new __bn.BN(x);}
var I_fromInt = I_fromNumber;
var I_fromBits = function(lo,hi) {
    var x = new __bn.BN(lo >>> 0);
    var y = new __bn.BN(hi >>> 0);
    y.ishln(32);
    x.iadd(y);
    return x;
}
var I_fromString = function(s) {return new __bn.BN(s);}
var I_toInt = function(x) {return I_toNumber(x.mod(__bn.MOD32));}
var I_toWord = function(x) {return I_toInt(x) >>> 0;};
// TODO: inefficient!
var I_toNumber = function(x) {return Number(x.toString());}
var I_equals = function(a,b) {return a.cmp(b) === 0;}
var I_compare = function(a,b) {return a.cmp(b);}
var I_compareInt = function(x,i) {return x.cmp(new __bn.BN(i));}
var I_negate = function(x) {return x.neg();}
var I_add = function(a,b) {return a.add(b);}
var I_sub = function(a,b) {return a.sub(b);}
var I_mul = function(a,b) {return a.mul(b);}
var I_mod = function(a,b) {return I_rem(I_add(b, I_rem(a, b)), b);}
var I_quotRem = function(a,b) {
    var qr = a.divmod(b);
    return {_:0, a:qr.div, b:qr.mod};
}
var I_div = function(a,b) {
    if((a.cmp(__bn.Z)>=0) != (a.cmp(__bn.Z)>=0)) {
        if(a.cmp(a.rem(b), __bn.Z) !== 0) {
            return a.div(b).sub(__bn.ONE);
        }
    }
    return a.div(b);
}
var I_divMod = function(a,b) {
    return {_:0, a:I_div(a,b), b:a.mod(b)};
}
var I_quot = function(a,b) {return a.div(b);}
var I_rem = function(a,b) {return a.mod(b);}
var I_and = function(a,b) {return a.and(b);}
var I_or = function(a,b) {return a.or(b);}
var I_xor = function(a,b) {return a.xor(b);}
var I_shiftLeft = function(a,b) {return a.shln(b);}
var I_shiftRight = function(a,b) {return a.shrn(b);}
var I_signum = function(x) {return x.cmp(new __bn.BN(0));}
var I_abs = function(x) {return x.abs();}
var I_decodeDouble = function(x) {
    var dec = decodeDouble(x);
    var mantissa = I_fromBits(dec.c, dec.b);
    if(dec.a < 0) {
        mantissa = I_negate(mantissa);
    }
    return {_:0, a:dec.d, b:mantissa};
}
var I_toString = function(x) {return x.toString();}
var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    if(x.isNegative()) {
        return I_negate(I_fromInt64(x.negate()));
    } else {
        return I_fromBits(x.low, x.high);
    }
}

function I_toInt64(x) {
    if(x.negative) {
        return I_toInt64(I_negate(x)).negate();
    } else {
        return new Long(I_toInt(x), I_toInt(I_shiftRight(x,32)));
    }
}

function I_fromWord64(x) {
    return I_fromBits(x.toInt(), x.shru(32).toInt());
}

function I_toWord64(x) {
    var w = I_toInt64(x);
    w.unsigned = true;
    return w;
}

/**
 * @license long.js (c) 2013 Daniel Wirtz <dcode@dcode.io>
 * Released under the Apache License, Version 2.0
 * see: https://github.com/dcodeIO/long.js for details
 */
function Long(low, high, unsigned) {
    this.low = low | 0;
    this.high = high | 0;
    this.unsigned = !!unsigned;
}

var INT_CACHE = {};
var UINT_CACHE = {};
function cacheable(x, u) {
    return u ? 0 <= (x >>>= 0) && x < 256 : -128 <= (x |= 0) && x < 128;
}

function __fromInt(value, unsigned) {
    var obj, cachedObj, cache;
    if (unsigned) {
        if (cache = cacheable(value >>>= 0, true)) {
            cachedObj = UINT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, (value | 0) < 0 ? -1 : 0, true);
        if (cache)
            UINT_CACHE[value] = obj;
        return obj;
    } else {
        if (cache = cacheable(value |= 0, false)) {
            cachedObj = INT_CACHE[value];
            if (cachedObj)
                return cachedObj;
        }
        obj = new Long(value, value < 0 ? -1 : 0, false);
        if (cache)
            INT_CACHE[value] = obj;
        return obj;
    }
}

function __fromNumber(value, unsigned) {
    if (isNaN(value) || !isFinite(value))
        return unsigned ? UZERO : ZERO;
    if (unsigned) {
        if (value < 0)
            return UZERO;
        if (value >= TWO_PWR_64_DBL)
            return MAX_UNSIGNED_VALUE;
    } else {
        if (value <= -TWO_PWR_63_DBL)
            return MIN_VALUE;
        if (value + 1 >= TWO_PWR_63_DBL)
            return MAX_VALUE;
    }
    if (value < 0)
        return __fromNumber(-value, unsigned).neg();
    return new Long((value % TWO_PWR_32_DBL) | 0, (value / TWO_PWR_32_DBL) | 0, unsigned);
}
var pow_dbl = Math.pow;
var TWO_PWR_16_DBL = 1 << 16;
var TWO_PWR_24_DBL = 1 << 24;
var TWO_PWR_32_DBL = TWO_PWR_16_DBL * TWO_PWR_16_DBL;
var TWO_PWR_64_DBL = TWO_PWR_32_DBL * TWO_PWR_32_DBL;
var TWO_PWR_63_DBL = TWO_PWR_64_DBL / 2;
var TWO_PWR_24 = __fromInt(TWO_PWR_24_DBL);
var ZERO = __fromInt(0);
Long.ZERO = ZERO;
var UZERO = __fromInt(0, true);
Long.UZERO = UZERO;
var ONE = __fromInt(1);
Long.ONE = ONE;
var UONE = __fromInt(1, true);
Long.UONE = UONE;
var NEG_ONE = __fromInt(-1);
Long.NEG_ONE = NEG_ONE;
var MAX_VALUE = new Long(0xFFFFFFFF|0, 0x7FFFFFFF|0, false);
Long.MAX_VALUE = MAX_VALUE;
var MAX_UNSIGNED_VALUE = new Long(0xFFFFFFFF|0, 0xFFFFFFFF|0, true);
Long.MAX_UNSIGNED_VALUE = MAX_UNSIGNED_VALUE;
var MIN_VALUE = new Long(0, 0x80000000|0, false);
Long.MIN_VALUE = MIN_VALUE;
var __lp = Long.prototype;
__lp.toInt = function() {return this.unsigned ? this.low >>> 0 : this.low;};
__lp.toNumber = function() {
    if (this.unsigned)
        return ((this.high >>> 0) * TWO_PWR_32_DBL) + (this.low >>> 0);
    return this.high * TWO_PWR_32_DBL + (this.low >>> 0);
};
__lp.isZero = function() {return this.high === 0 && this.low === 0;};
__lp.isNegative = function() {return !this.unsigned && this.high < 0;};
__lp.isOdd = function() {return (this.low & 1) === 1;};
__lp.eq = function(other) {
    if (this.unsigned !== other.unsigned && (this.high >>> 31) === 1 && (other.high >>> 31) === 1)
        return false;
    return this.high === other.high && this.low === other.low;
};
__lp.neq = function(other) {return !this.eq(other);};
__lp.lt = function(other) {return this.comp(other) < 0;};
__lp.lte = function(other) {return this.comp(other) <= 0;};
__lp.gt = function(other) {return this.comp(other) > 0;};
__lp.gte = function(other) {return this.comp(other) >= 0;};
__lp.compare = function(other) {
    if (this.eq(other))
        return 0;
    var thisNeg = this.isNegative(),
        otherNeg = other.isNegative();
    if (thisNeg && !otherNeg)
        return -1;
    if (!thisNeg && otherNeg)
        return 1;
    if (!this.unsigned)
        return this.sub(other).isNegative() ? -1 : 1;
    return (other.high >>> 0) > (this.high >>> 0) || (other.high === this.high && (other.low >>> 0) > (this.low >>> 0)) ? -1 : 1;
};
__lp.comp = __lp.compare;
__lp.negate = function() {
    if (!this.unsigned && this.eq(MIN_VALUE))
        return MIN_VALUE;
    return this.not().add(ONE);
};
__lp.neg = __lp.negate;
__lp.add = function(addend) {
    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = addend.high >>> 16;
    var b32 = addend.high & 0xFFFF;
    var b16 = addend.low >>> 16;
    var b00 = addend.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 + b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 + b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 + b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 + b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.subtract = function(subtrahend) {return this.add(subtrahend.neg());};
__lp.sub = __lp.subtract;
__lp.multiply = function(multiplier) {
    if (this.isZero())
        return ZERO;
    if (multiplier.isZero())
        return ZERO;
    if (this.eq(MIN_VALUE))
        return multiplier.isOdd() ? MIN_VALUE : ZERO;
    if (multiplier.eq(MIN_VALUE))
        return this.isOdd() ? MIN_VALUE : ZERO;

    if (this.isNegative()) {
        if (multiplier.isNegative())
            return this.neg().mul(multiplier.neg());
        else
            return this.neg().mul(multiplier).neg();
    } else if (multiplier.isNegative())
        return this.mul(multiplier.neg()).neg();

    if (this.lt(TWO_PWR_24) && multiplier.lt(TWO_PWR_24))
        return __fromNumber(this.toNumber() * multiplier.toNumber(), this.unsigned);

    var a48 = this.high >>> 16;
    var a32 = this.high & 0xFFFF;
    var a16 = this.low >>> 16;
    var a00 = this.low & 0xFFFF;

    var b48 = multiplier.high >>> 16;
    var b32 = multiplier.high & 0xFFFF;
    var b16 = multiplier.low >>> 16;
    var b00 = multiplier.low & 0xFFFF;

    var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
    c00 += a00 * b00;
    c16 += c00 >>> 16;
    c00 &= 0xFFFF;
    c16 += a16 * b00;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c16 += a00 * b16;
    c32 += c16 >>> 16;
    c16 &= 0xFFFF;
    c32 += a32 * b00;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a16 * b16;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c32 += a00 * b32;
    c48 += c32 >>> 16;
    c32 &= 0xFFFF;
    c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
    c48 &= 0xFFFF;
    return new Long((c16 << 16) | c00, (c48 << 16) | c32, this.unsigned);
};
__lp.mul = __lp.multiply;
__lp.divide = function(divisor) {
    if (divisor.isZero())
        throw Error('division by zero');
    if (this.isZero())
        return this.unsigned ? UZERO : ZERO;
    var approx, rem, res;
    if (this.eq(MIN_VALUE)) {
        if (divisor.eq(ONE) || divisor.eq(NEG_ONE))
            return MIN_VALUE;
        else if (divisor.eq(MIN_VALUE))
            return ONE;
        else {
            var halfThis = this.shr(1);
            approx = halfThis.div(divisor).shl(1);
            if (approx.eq(ZERO)) {
                return divisor.isNegative() ? ONE : NEG_ONE;
            } else {
                rem = this.sub(divisor.mul(approx));
                res = approx.add(rem.div(divisor));
                return res;
            }
        }
    } else if (divisor.eq(MIN_VALUE))
        return this.unsigned ? UZERO : ZERO;
    if (this.isNegative()) {
        if (divisor.isNegative())
            return this.neg().div(divisor.neg());
        return this.neg().div(divisor).neg();
    } else if (divisor.isNegative())
        return this.div(divisor.neg()).neg();

    res = ZERO;
    rem = this;
    while (rem.gte(divisor)) {
        approx = Math.max(1, Math.floor(rem.toNumber() / divisor.toNumber()));
        var log2 = Math.ceil(Math.log(approx) / Math.LN2),
            delta = (log2 <= 48) ? 1 : pow_dbl(2, log2 - 48),
            approxRes = __fromNumber(approx),
            approxRem = approxRes.mul(divisor);
        while (approxRem.isNegative() || approxRem.gt(rem)) {
            approx -= delta;
            approxRes = __fromNumber(approx, this.unsigned);
            approxRem = approxRes.mul(divisor);
        }
        if (approxRes.isZero())
            approxRes = ONE;

        res = res.add(approxRes);
        rem = rem.sub(approxRem);
    }
    return res;
};
__lp.div = __lp.divide;
__lp.modulo = function(divisor) {return this.sub(this.div(divisor).mul(divisor));};
__lp.mod = __lp.modulo;
__lp.not = function not() {return new Long(~this.low, ~this.high, this.unsigned);};
__lp.and = function(other) {return new Long(this.low & other.low, this.high & other.high, this.unsigned);};
__lp.or = function(other) {return new Long(this.low | other.low, this.high | other.high, this.unsigned);};
__lp.xor = function(other) {return new Long(this.low ^ other.low, this.high ^ other.high, this.unsigned);};

__lp.shl = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long(this.low << numBits, (this.high << numBits) | (this.low >>> (32 - numBits)), this.unsigned);
    else
        return new Long(0, this.low << (numBits - 32), this.unsigned);
};

__lp.shr = function(numBits) {
    if ((numBits &= 63) === 0)
        return this;
    else if (numBits < 32)
        return new Long((this.low >>> numBits) | (this.high << (32 - numBits)), this.high >> numBits, this.unsigned);
    else
        return new Long(this.high >> (numBits - 32), this.high >= 0 ? 0 : -1, this.unsigned);
};

__lp.shru = function(numBits) {
    numBits &= 63;
    if (numBits === 0)
        return this;
    else {
        var high = this.high;
        if (numBits < 32) {
            var low = this.low;
            return new Long((low >>> numBits) | (high << (32 - numBits)), high >>> numBits, this.unsigned);
        } else if (numBits === 32)
            return new Long(high, 0, this.unsigned);
        else
            return new Long(high >>> (numBits - 32), 0, this.unsigned);
    }
};

__lp.toSigned = function() {return this.unsigned ? new Long(this.low, this.high, false) : this;};
__lp.toUnsigned = function() {return this.unsigned ? this : new Long(this.low, this.high, true);};

// Int64
function hs_eqInt64(x, y) {return x.eq(y);}
function hs_neInt64(x, y) {return x.neq(y);}
function hs_ltInt64(x, y) {return x.lt(y);}
function hs_leInt64(x, y) {return x.lte(y);}
function hs_gtInt64(x, y) {return x.gt(y);}
function hs_geInt64(x, y) {return x.gte(y);}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shl(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shr(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shru(bits);}
function hs_int64ToInt(x) {return x.toInt();}
var hs_intToInt64 = __fromInt;

// Word64
function hs_wordToWord64(x) {return __fromInt(x, true);}
function hs_word64ToWord(x) {return x.toInt(x);}
function hs_mkWord64(low, high) {return new Long(low,high,true);}
function hs_and64(a,b) {return a.and(b);};
function hs_or64(a,b) {return a.or(b);};
function hs_xor64(a,b) {return a.xor(b);};
function hs_not64(x) {return x.not();}
var hs_eqWord64 = hs_eqInt64;
var hs_neWord64 = hs_neInt64;
var hs_ltWord64 = hs_ltInt64;
var hs_leWord64 = hs_leInt64;
var hs_gtWord64 = hs_gtInt64;
var hs_geWord64 = hs_geInt64;
var hs_quotWord64 = hs_quotInt64;
var hs_remWord64 = hs_remInt64;
var hs_uncheckedShiftL64 = hs_uncheckedIShiftL64;
var hs_uncheckedShiftRL64 = hs_uncheckedIShiftRL64;
function hs_int64ToWord64(x) {return x.toUnsigned();}
function hs_word64ToInt64(x) {return x.toSigned();}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    return new ByteArray(new ArrayBuffer(n));
}

// Wrap a JS ArrayBuffer into a ByteArray. Truncates the array length to the
// closest multiple of 8 bytes.
function wrapByteArr(buffer) {
    var diff = buffer.byteLength % 8;
    if(diff != 0) {
        var buffer = buffer.slice(0, buffer.byteLength-diff);
    }
    return new ByteArray(buffer);
}

function ByteArray(buffer) {
    var views =
        { 'i8' : new Int8Array(buffer)
        , 'i16': new Int16Array(buffer)
        , 'i32': new Int32Array(buffer)
        , 'w8' : new Uint8Array(buffer)
        , 'w16': new Uint16Array(buffer)
        , 'w32': new Uint32Array(buffer)
        , 'f32': new Float32Array(buffer)
        , 'f64': new Float64Array(buffer)
        };
    this['b'] = buffer;
    this['v'] = views;
    this['off'] = 0;
}
window['newArr'] = newArr;
window['newByteArr'] = newByteArr;
window['wrapByteArr'] = wrapByteArr;
window['ByteArray'] = ByteArray;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function writeOffAddr64(addr, off, x) {
    addr['v']['w32'][addr.off/8 + off*2] = x.low;
    addr['v']['w32'][addr.off/8 + off*2 + 1] = x.high;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

function readOffAddr64(signed, addr, off) {
    var w64 = hs_mkWord64( addr['v']['w32'][addr.off/8 + off*2]
                         , addr['v']['w32'][addr.off/8 + off*2 + 1]);
    return signed ? hs_word64ToInt64(w64) : w64;
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return {_:0, a:1, b:E(w).val};
}

function finalizeWeak(w) {
    return {_:0, a:B(A1(E(w).fin, __Z))};
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as._ === 1; as = as.b) {
        arr.push(as.a);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return __Z;
    }
    return {_:1,
            a:arr[elem],
            b:new T(function(){return __arr2lst(elem+1,arr);})};
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs._ === 1; xs = E(xs.b)) {
        arr.push(E(xs.a));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0/* () */ = 0,
_1/* $fFromAny()4 */ = function(_/* EXTERNAL */){
  return _0/* GHC.Tuple.() */;
},
_2/* Just */ = function(_3/* B1 */){
  return new T1(1,_3/* B1 */);
},
_4/* id */ = function(_5/* s3aI */){
  return E(_5/* s3aI */);
},
_6/* $fJSTypeJSString */ = new T2(0,_4/* GHC.Base.id */,_2/* GHC.Base.Just */),
_7/* fromJSStr */ = function(_8/* sdrS */){
  return new F(function(){return fromJSStr/* EXTERNAL */(E(_8/* sdrS */));});
},
_9/* $fJSType[]_$cfromJSString */ = function(_a/* s3BE */){
  return new T1(1,new T(function(){
    return B(_7/* GHC.HastePrim.fromJSStr */(_a/* s3BE */));
  }));
},
_b/* toJSStr1 */ = function(_c/* sdrX */){
  return new F(function(){return toJSStr/* EXTERNAL */(E(_c/* sdrX */));});
},
_d/* $fJSType[] */ = new T2(0,_b/* GHC.HastePrim.toJSStr1 */,_9/* Haste.Prim.JSType.$fJSType[]_$cfromJSString */),
_e/* $fApplicativeIO1 */ = function(_f/* s3hg */, _g/* s3hh */, _/* EXTERNAL */){
  var _h/* s3hj */ = B(A1(_f/* s3hg */,_/* EXTERNAL */)),
  _i/* s3hm */ = B(A1(_g/* s3hh */,_/* EXTERNAL */));
  return _h/* s3hj */;
},
_j/* $fApplicativeIO2 */ = function(_k/* s3gu */, _l/* s3gv */, _/* EXTERNAL */){
  var _m/* s3gx */ = B(A1(_k/* s3gu */,_/* EXTERNAL */)),
  _n/* s3gA */ = B(A1(_l/* s3gv */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_m/* s3gx */,_n/* s3gA */));
  });
},
_o/* $fFunctorIO1 */ = function(_p/* s3gZ */, _q/* s3h0 */, _/* EXTERNAL */){
  var _r/* s3h2 */ = B(A1(_q/* s3h0 */,_/* EXTERNAL */));
  return _p/* s3gZ */;
},
_s/* $fFunctorIO2 */ = function(_t/* s3gS */, _u/* s3gT */, _/* EXTERNAL */){
  var _v/* s3gV */ = B(A1(_u/* s3gT */,_/* EXTERNAL */));
  return new T(function(){
    return B(A1(_t/* s3gS */,_v/* s3gV */));
  });
},
_w/* $fFunctorIO */ = new T2(0,_s/* GHC.Base.$fFunctorIO2 */,_o/* GHC.Base.$fFunctorIO1 */),
_x/* returnIO1 */ = function(_y/* s3g7 */, _/* EXTERNAL */){
  return _y/* s3g7 */;
},
_z/* thenIO1 */ = function(_A/* s3g1 */, _B/* s3g2 */, _/* EXTERNAL */){
  var _C/* s3g4 */ = B(A1(_A/* s3g1 */,_/* EXTERNAL */));
  return new F(function(){return A1(_B/* s3g2 */,_/* EXTERNAL */);});
},
_D/* $fApplicativeIO */ = new T5(0,_w/* GHC.Base.$fFunctorIO */,_x/* GHC.Base.returnIO1 */,_j/* GHC.Base.$fApplicativeIO2 */,_z/* GHC.Base.thenIO1 */,_e/* GHC.Base.$fApplicativeIO1 */),
_E/* $fExceptionAllocationLimitExceeded_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_F/* $fExceptionAllocationLimitExceeded_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.IO.Exception"));
}),
_G/* $fExceptionIOException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IOException"));
}),
_H/* $fExceptionIOException_wild */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_E/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww2 */,_F/* GHC.IO.Exception.$fExceptionAllocationLimitExceeded_ww4 */,_G/* GHC.IO.Exception.$fExceptionIOException_ww4 */),
_I/* [] */ = __Z/* EXTERNAL */,
_J/* $fExceptionIOException4 */ = new T5(0,new Long/* EXTERNAL */(4053623282, 1685460941, true),new Long/* EXTERNAL */(3693590983, 2507416641, true),_H/* GHC.IO.Exception.$fExceptionIOException_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_K/* $fExceptionIOException3 */ = function(_L/* s3K6Q */){
  return E(_J/* GHC.IO.Exception.$fExceptionIOException4 */);
},
_M/* $p1Exception */ = function(_N/* s2Szo */){
  return E(E(_N/* s2Szo */).a);
},
_O/* cast */ = function(_P/* s26is */, _Q/* s26it */, _R/* s26iu */){
  var _S/* s26iv */ = B(A1(_P/* s26is */,_/* EXTERNAL */)),
  _T/* s26iB */ = B(A1(_Q/* s26it */,_/* EXTERNAL */)),
  _U/* s26iI */ = hs_eqWord64/* EXTERNAL */(_S/* s26iv */.a, _T/* s26iB */.a);
  if(!_U/* s26iI */){
    return __Z/* EXTERNAL */;
  }else{
    var _V/* s26iN */ = hs_eqWord64/* EXTERNAL */(_S/* s26iv */.b, _T/* s26iB */.b);
    return (!_V/* s26iN */) ? __Z/* EXTERNAL */ : new T1(1,_R/* s26iu */);
  }
},
_W/* $fExceptionIOException_$cfromException */ = function(_X/* s3KaB */){
  var _Y/* s3KaC */ = E(_X/* s3KaB */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_Y/* s3KaC */.a)), _K/* GHC.IO.Exception.$fExceptionIOException3 */, _Y/* s3KaC */.b);});
},
_Z/* $fExceptionArrayException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": "));
}),
_10/* $fExceptionIOException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_11/* $fExceptionIOException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" ("));
}),
_12/* ++ */ = function(_13/* s3hJ */, _14/* s3hK */){
  var _15/* s3hL */ = E(_13/* s3hJ */);
  return (_15/* s3hL */._==0) ? E(_14/* s3hK */) : new T2(1,_15/* s3hL */.a,new T(function(){
    return B(_12/* GHC.Base.++ */(_15/* s3hL */.b, _14/* s3hK */));
  }));
},
_16/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("interrupted"));
}),
_17/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("system error"));
}),
_18/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsatisified constraints"));
}),
_19/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("user error"));
}),
_1a/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("permission denied"));
}),
_1b/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("illegal operation"));
}),
_1c/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("end of file"));
}),
_1d/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource exhausted"));
}),
_1e/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource busy"));
}),
_1f/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("does not exist"));
}),
_1g/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("already exists"));
}),
_1h/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("resource vanished"));
}),
_1i/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("timeout"));
}),
_1j/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("unsupported operation"));
}),
_1k/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hardware fault"));
}),
_1l/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inappropriate type"));
}),
_1m/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid argument"));
}),
_1n/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("failed"));
}),
_1o/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("protocol error"));
}),
_1p/* $w$cshowsPrec3 */ = function(_1q/* s3Kcg */, _1r/* s3Kch */){
  switch(E(_1q/* s3Kcg */)){
    case 0:
      return new F(function(){return _12/* GHC.Base.++ */(_1g/* GHC.IO.Exception.lvl19 */, _1r/* s3Kch */);});
      break;
    case 1:
      return new F(function(){return _12/* GHC.Base.++ */(_1f/* GHC.IO.Exception.lvl18 */, _1r/* s3Kch */);});
      break;
    case 2:
      return new F(function(){return _12/* GHC.Base.++ */(_1e/* GHC.IO.Exception.lvl17 */, _1r/* s3Kch */);});
      break;
    case 3:
      return new F(function(){return _12/* GHC.Base.++ */(_1d/* GHC.IO.Exception.lvl16 */, _1r/* s3Kch */);});
      break;
    case 4:
      return new F(function(){return _12/* GHC.Base.++ */(_1c/* GHC.IO.Exception.lvl15 */, _1r/* s3Kch */);});
      break;
    case 5:
      return new F(function(){return _12/* GHC.Base.++ */(_1b/* GHC.IO.Exception.lvl14 */, _1r/* s3Kch */);});
      break;
    case 6:
      return new F(function(){return _12/* GHC.Base.++ */(_1a/* GHC.IO.Exception.lvl13 */, _1r/* s3Kch */);});
      break;
    case 7:
      return new F(function(){return _12/* GHC.Base.++ */(_19/* GHC.IO.Exception.lvl12 */, _1r/* s3Kch */);});
      break;
    case 8:
      return new F(function(){return _12/* GHC.Base.++ */(_18/* GHC.IO.Exception.lvl11 */, _1r/* s3Kch */);});
      break;
    case 9:
      return new F(function(){return _12/* GHC.Base.++ */(_17/* GHC.IO.Exception.lvl10 */, _1r/* s3Kch */);});
      break;
    case 10:
      return new F(function(){return _12/* GHC.Base.++ */(_1o/* GHC.IO.Exception.lvl9 */, _1r/* s3Kch */);});
      break;
    case 11:
      return new F(function(){return _12/* GHC.Base.++ */(_1n/* GHC.IO.Exception.lvl8 */, _1r/* s3Kch */);});
      break;
    case 12:
      return new F(function(){return _12/* GHC.Base.++ */(_1m/* GHC.IO.Exception.lvl7 */, _1r/* s3Kch */);});
      break;
    case 13:
      return new F(function(){return _12/* GHC.Base.++ */(_1l/* GHC.IO.Exception.lvl6 */, _1r/* s3Kch */);});
      break;
    case 14:
      return new F(function(){return _12/* GHC.Base.++ */(_1k/* GHC.IO.Exception.lvl5 */, _1r/* s3Kch */);});
      break;
    case 15:
      return new F(function(){return _12/* GHC.Base.++ */(_1j/* GHC.IO.Exception.lvl4 */, _1r/* s3Kch */);});
      break;
    case 16:
      return new F(function(){return _12/* GHC.Base.++ */(_1i/* GHC.IO.Exception.lvl3 */, _1r/* s3Kch */);});
      break;
    case 17:
      return new F(function(){return _12/* GHC.Base.++ */(_1h/* GHC.IO.Exception.lvl2 */, _1r/* s3Kch */);});
      break;
    default:
      return new F(function(){return _12/* GHC.Base.++ */(_16/* GHC.IO.Exception.lvl1 */, _1r/* s3Kch */);});
  }
},
_1s/* showHandle1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("}"));
}),
_1t/* showHandle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("{handle: "));
}),
_1u/* $w$cshowsPrec2 */ = function(_1v/* s3Kcp */, _1w/* s3Kcq */, _1x/* s3Kcr */, _1y/* s3Kcs */, _1z/* s3Kct */, _1A/* s3Kcu */){
  var _1B/* s3Kcv */ = new T(function(){
    var _1C/* s3Kcw */ = new T(function(){
      var _1D/* s3KcC */ = new T(function(){
        var _1E/* s3Kcx */ = E(_1y/* s3Kcs */);
        if(!_1E/* s3Kcx */._){
          return E(_1A/* s3Kcu */);
        }else{
          var _1F/* s3KcB */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_1E/* s3Kcx */, new T(function(){
              return B(_12/* GHC.Base.++ */(_10/* GHC.IO.Exception.$fExceptionIOException1 */, _1A/* s3Kcu */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(_11/* GHC.IO.Exception.$fExceptionIOException2 */, _1F/* s3KcB */));
        }
      },1);
      return B(_1p/* GHC.IO.Exception.$w$cshowsPrec3 */(_1w/* s3Kcq */, _1D/* s3KcC */));
    }),
    _1G/* s3KcD */ = E(_1x/* s3Kcr */);
    if(!_1G/* s3KcD */._){
      return E(_1C/* s3Kcw */);
    }else{
      return B(_12/* GHC.Base.++ */(_1G/* s3KcD */, new T(function(){
        return B(_12/* GHC.Base.++ */(_Z/* GHC.IO.Exception.$fExceptionArrayException2 */, _1C/* s3Kcw */));
      },1)));
    }
  }),
  _1H/* s3KcH */ = E(_1z/* s3Kct */);
  if(!_1H/* s3KcH */._){
    var _1I/* s3KcI */ = E(_1v/* s3Kcp */);
    if(!_1I/* s3KcI */._){
      return E(_1B/* s3Kcv */);
    }else{
      var _1J/* s3KcK */ = E(_1I/* s3KcI */.a);
      if(!_1J/* s3KcK */._){
        var _1K/* s3KcP */ = new T(function(){
          var _1L/* s3KcO */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_1s/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_12/* GHC.Base.++ */(_Z/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3Kcv */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(_1J/* s3KcK */.a, _1L/* s3KcO */));
        },1);
        return new F(function(){return _12/* GHC.Base.++ */(_1t/* GHC.IO.Handle.Types.showHandle2 */, _1K/* s3KcP */);});
      }else{
        var _1M/* s3KcV */ = new T(function(){
          var _1N/* s3KcU */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_1s/* GHC.IO.Handle.Types.showHandle1 */, new T(function(){
              return B(_12/* GHC.Base.++ */(_Z/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3Kcv */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(_1J/* s3KcK */.a, _1N/* s3KcU */));
        },1);
        return new F(function(){return _12/* GHC.Base.++ */(_1t/* GHC.IO.Handle.Types.showHandle2 */, _1M/* s3KcV */);});
      }
    }
  }else{
    return new F(function(){return _12/* GHC.Base.++ */(_1H/* s3KcH */.a, new T(function(){
      return B(_12/* GHC.Base.++ */(_Z/* GHC.IO.Exception.$fExceptionArrayException2 */, _1B/* s3Kcv */));
    },1));});
  }
},
_1O/* $fExceptionIOException_$cshow */ = function(_1P/* s3Kd8 */){
  var _1Q/* s3Kd9 */ = E(_1P/* s3Kd8 */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_1Q/* s3Kd9 */.a, _1Q/* s3Kd9 */.b, _1Q/* s3Kd9 */.c, _1Q/* s3Kd9 */.d, _1Q/* s3Kd9 */.f, _I/* GHC.Types.[] */);});
},
_1R/* $fExceptionIOException_$ctoException */ = function(_1S/* B1 */){
  return new T2(0,_1T/* GHC.IO.Exception.$fExceptionIOException */,_1S/* B1 */);
},
_1U/* $fExceptionIOException_$cshowsPrec */ = function(_1V/* s3KcY */, _1W/* s3KcZ */, _1X/* s3Kd0 */){
  var _1Y/* s3Kd1 */ = E(_1W/* s3KcZ */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_1Y/* s3Kd1 */.a, _1Y/* s3Kd1 */.b, _1Y/* s3Kd1 */.c, _1Y/* s3Kd1 */.d, _1Y/* s3Kd1 */.f, _1X/* s3Kd0 */);});
},
_1Z/* $s$dmshow9 */ = function(_20/* s3Kdg */, _21/* s3Kdh */){
  var _22/* s3Kdi */ = E(_20/* s3Kdg */);
  return new F(function(){return _1u/* GHC.IO.Exception.$w$cshowsPrec2 */(_22/* s3Kdi */.a, _22/* s3Kdi */.b, _22/* s3Kdi */.c, _22/* s3Kdi */.d, _22/* s3Kdi */.f, _21/* s3Kdh */);});
},
_23/* showList__1 */ = 44,
_24/* showList__2 */ = 93,
_25/* showList__3 */ = 91,
_26/* showList__ */ = function(_27/* sfc2 */, _28/* sfc3 */, _29/* sfc4 */){
  var _2a/* sfc5 */ = E(_28/* sfc3 */);
  if(!_2a/* sfc5 */._){
    return new F(function(){return unAppCStr/* EXTERNAL */("[]", _29/* sfc4 */);});
  }else{
    var _2b/* sfch */ = new T(function(){
      var _2c/* sfcg */ = new T(function(){
        var _2d/* sfc9 */ = function(_2e/* sfca */){
          var _2f/* sfcb */ = E(_2e/* sfca */);
          if(!_2f/* sfcb */._){
            return E(new T2(1,_24/* GHC.Show.showList__2 */,_29/* sfc4 */));
          }else{
            var _2g/* sfcf */ = new T(function(){
              return B(A2(_27/* sfc2 */,_2f/* sfcb */.a, new T(function(){
                return B(_2d/* sfc9 */(_2f/* sfcb */.b));
              })));
            });
            return new T2(1,_23/* GHC.Show.showList__1 */,_2g/* sfcf */);
          }
        };
        return B(_2d/* sfc9 */(_2a/* sfc5 */.b));
      });
      return B(A2(_27/* sfc2 */,_2a/* sfc5 */.a, _2c/* sfcg */));
    });
    return new T2(1,_25/* GHC.Show.showList__3 */,_2b/* sfch */);
  }
},
_2h/* $fShowIOException_$cshowList */ = function(_2i/* s3Kdp */, _2j/* s3Kdq */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_1Z/* GHC.IO.Exception.$s$dmshow9 */, _2i/* s3Kdp */, _2j/* s3Kdq */);});
},
_2k/* $fShowIOException */ = new T3(0,_1U/* GHC.IO.Exception.$fExceptionIOException_$cshowsPrec */,_1O/* GHC.IO.Exception.$fExceptionIOException_$cshow */,_2h/* GHC.IO.Exception.$fShowIOException_$cshowList */),
_1T/* $fExceptionIOException */ = new T(function(){
  return new T5(0,_K/* GHC.IO.Exception.$fExceptionIOException3 */,_2k/* GHC.IO.Exception.$fShowIOException */,_1R/* GHC.IO.Exception.$fExceptionIOException_$ctoException */,_W/* GHC.IO.Exception.$fExceptionIOException_$cfromException */,_1O/* GHC.IO.Exception.$fExceptionIOException_$cshow */);
}),
_2l/* $fxExceptionIOException */ = new T(function(){
  return E(_1T/* GHC.IO.Exception.$fExceptionIOException */);
}),
_2m/* toException */ = function(_2n/* s2SzC */){
  return E(E(_2n/* s2SzC */).c);
},
_2o/* Nothing */ = __Z/* EXTERNAL */,
_2p/* UserError */ = 7,
_2q/* userError */ = function(_2r/* s3K6P */){
  return new T6(0,_2o/* GHC.Base.Nothing */,_2p/* GHC.IO.Exception.UserError */,_I/* GHC.Types.[] */,_2r/* s3K6P */,_2o/* GHC.Base.Nothing */,_2o/* GHC.Base.Nothing */);
},
_2s/* failIO1 */ = function(_2t/* s2WaY */, _/* EXTERNAL */){
  var _2u/* s2Wb1 */ = new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_2l/* GHC.IO.Exception.$fxExceptionIOException */, new T(function(){
      return B(A1(_2q/* GHC.IO.Exception.userError */,_2t/* s2WaY */));
    })));
  });
  return new F(function(){return die/* EXTERNAL */(_2u/* s2Wb1 */);});
},
_2v/* failIO */ = function(_2w/* B2 */, _/* EXTERNAL */){
  return new F(function(){return _2s/* GHC.IO.failIO1 */(_2w/* B2 */, _/* EXTERNAL */);});
},
_2x/* $fMonadIO_$cfail */ = function(_2y/* s3ek */){
  return new F(function(){return A1(_2v/* GHC.IO.failIO */,_2y/* s3ek */);});
},
_2z/* bindIO1 */ = function(_2A/* s3g9 */, _2B/* s3ga */, _/* EXTERNAL */){
  var _2C/* s3gc */ = B(A1(_2A/* s3g9 */,_/* EXTERNAL */));
  return new F(function(){return A2(_2B/* s3ga */,_2C/* s3gc */, _/* EXTERNAL */);});
},
_2D/* $fMonadIO */ = new T5(0,_D/* GHC.Base.$fApplicativeIO */,_2z/* GHC.Base.bindIO1 */,_z/* GHC.Base.thenIO1 */,_x/* GHC.Base.returnIO1 */,_2x/* GHC.Base.$fMonadIO_$cfail */),
_2E/* $fMonadIOIO */ = new T2(0,_2D/* GHC.Base.$fMonadIO */,_4/* GHC.Base.id */),
_2F/* POST */ = 1,
_2G/* False */ = false,
_2H/* pageTabGroup10 */ = 0,
_2I/* pageTabGroup37 */ = 200,
_2J/* pageTabGroup36 */ = new T2(1,_2I/* Page.pageTabGroup37 */,_I/* GHC.Types.[] */),
_2K/* pageTabGroup35 */ = new T2(1,_2J/* Page.pageTabGroup36 */,_2H/* Page.pageTabGroup10 */),
_2L/* pageTabGroup34 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_2K/* Page.pageTabGroup35 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_2M/* pageTabGroup33 */ = new T2(7,_2L/* Page.pageTabGroup34 */,_I/* GHC.Types.[] */),
_2N/* actionTab */ = new T3(0,_2M/* Page.pageTabGroup33 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_2O/* $fToAnyMethod1 */ = "POST",
_2P/* $fToAnyMethod2 */ = "GET",
_2Q/* lvl2 */ = "=",
_2R/* lvl3 */ = "&",
_2S/* map */ = function(_2T/* s3ht */, _2U/* s3hu */){
  var _2V/* s3hv */ = E(_2U/* s3hu */);
  return (_2V/* s3hv */._==0) ? __Z/* EXTERNAL */ : new T2(1,new T(function(){
    return B(A1(_2T/* s3ht */,_2V/* s3hv */.a));
  }),new T(function(){
    return B(_2S/* GHC.Base.map */(_2T/* s3ht */, _2V/* s3hv */.b));
  }));
},
_2W/* toJSString */ = function(_2X/* s3zz */){
  return E(E(_2X/* s3zz */).a);
},
_2Y/* $wtoQueryString */ = function(_2Z/* sd4I */, _30/* sd4J */, _31/* sd4K */){
  var _32/* sd50 */ = function(_33/* sd4L */){
    var _34/* sd4M */ = E(_33/* sd4L */);
    return new F(function(){return jsCat/* EXTERNAL */(new T2(1,new T(function(){
      return B(A2(_2W/* Haste.Prim.JSType.toJSString */,_2Z/* sd4I */, _34/* sd4M */.a));
    }),new T2(1,new T(function(){
      return B(A2(_2W/* Haste.Prim.JSType.toJSString */,_30/* sd4J */, _34/* sd4M */.b));
    }),_I/* GHC.Types.[] */)), E(_2Q/* Haste.Ajax.lvl2 */));});
  },
  _35/* sd56 */ = jsCat/* EXTERNAL */(B(_2S/* GHC.Base.map */(_32/* sd50 */, _31/* sd4K */)), E(_2R/* Haste.Ajax.lvl3 */));
  return E(_35/* sd56 */);
},
_36/* f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == \'POST\') {xhr.setRequestHeader(\'Content-type\',\'application/x-www-form-urlencoded\');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);})");
}),
_37/* fromJSString */ = function(_38/* s3zD */){
  return E(E(_38/* s3zD */).b);
},
_39/* lvl2 */ = function(_/* EXTERNAL */){
  return new F(function(){return __jsNull/* EXTERNAL */();});
},
_3a/* unsafeDupablePerformIO */ = function(_3b/* s2Wdd */){
  var _3c/* s2Wde */ = B(A1(_3b/* s2Wdd */,_/* EXTERNAL */));
  return E(_3c/* s2Wde */);
},
_3d/* nullValue */ = new T(function(){
  return B(_3a/* GHC.IO.unsafeDupablePerformIO */(_39/* Haste.Prim.Any.lvl2 */));
}),
_3e/* jsNull */ = new T(function(){
  return E(_3d/* Haste.Prim.Any.nullValue */);
}),
_3f/* liftIO */ = function(_3g/* stz */){
  return E(E(_3g/* stz */).b);
},
_3h/* lvl */ = new T(function(){
  return toJSStr/* EXTERNAL */(_I/* GHC.Types.[] */);
}),
_3i/* lvl1 */ = "?",
_3j/* ajaxRequest */ = function(_3k/* sd5x */, _3l/* sd5y */, _3m/* sd5z */, _3n/* sd5A */, _3o/* sd5B */, _3p/* sd5C */, _3q/* sd5D */, _3r/* sd5E */){
  var _3s/* sd5H */ = new T(function(){
    return B(_2Y/* Haste.Ajax.$wtoQueryString */(_3l/* sd5y */, _3m/* sd5z */, _3q/* sd5D */));
  }),
  _3t/* sd5F */ = new T(function(){
    return B(_b/* GHC.HastePrim.toJSStr1 */(_3p/* sd5C */));
  }),
  _3u/* sd70 */ = function(_/* EXTERNAL */){
    var _3v/* sd5M */ = function(_3w/* sd5N */){
      var _3x/* sd5O */ = function(_3y/* sd5P */){
        var _3z/* sd5Q */ = function(_3A/* sd5R */){
          var _3B/* sd5S */ = new T(function(){
            return B(_37/* Haste.Prim.JSType.fromJSString */(_3n/* sd5A */));
          }),
          _3C/* sd6d */ = function(_3D/* sd5T */, _/* EXTERNAL */){
            var _3E/* sd69 */ = new T(function(){
              var _3F/* sd5V */ = E(_3D/* sd5T */),
              _3G/* sd60 */ = __eq/* EXTERNAL */(_3F/* sd5V */, E(_3e/* Haste.Prim.Any.jsNull */));
              if(!E(_3G/* sd60 */)){
                return B(A1(_3B/* sd5S */,new T(function(){
                  return String/* EXTERNAL */(_3F/* sd5V */);
                })));
              }else{
                return __Z/* EXTERNAL */;
              }
            }),
            _3H/* sd6a */ = B(A2(_3r/* sd5E */,_3E/* sd69 */, _/* EXTERNAL */));
            return _3e/* Haste.Prim.Any.jsNull */;
          },
          _3I/* sd6h */ = __createJSFunc/* EXTERNAL */(2, E(_3C/* sd6d */)),
          _3J/* sd6p */ = __app5/* EXTERNAL */(E(_36/* Haste.Ajax.f1 */), _3w/* sd5N */, _3y/* sd5P */, true, _3A/* sd5R */, _3I/* sd6h */);
          return _0/* GHC.Tuple.() */;
        };
        if(!E(_3o/* sd5B */)){
          return new F(function(){return _3z/* sd5Q */(E(_3h/* Haste.Ajax.lvl */));});
        }else{
          var _3K/* sd6v */ = E(_3q/* sd5D */);
          if(!_3K/* sd6v */._){
            return new F(function(){return _3z/* sd5Q */(E(_3h/* Haste.Ajax.lvl */));});
          }else{
            return new F(function(){return _3z/* sd5Q */(B(_2Y/* Haste.Ajax.$wtoQueryString */(_3l/* sd5y */, _3m/* sd5z */, _3K/* sd6v */)));});
          }
        }
      };
      if(!E(_3o/* sd5B */)){
        if(!E(_3q/* sd5D */)._){
          return new F(function(){return _3x/* sd5O */(toJSStr/* EXTERNAL */(E(_3p/* sd5C */)));});
        }else{
          var _3L/* sd6N */ = jsCat/* EXTERNAL */(new T2(1,_3t/* sd5F */,new T2(1,_3s/* sd5H */,_I/* GHC.Types.[] */)), E(_3i/* Haste.Ajax.lvl1 */));
          return new F(function(){return _3x/* sd5O */(_3L/* sd6N */);});
        }
      }else{
        return new F(function(){return _3x/* sd5O */(toJSStr/* EXTERNAL */(E(_3p/* sd5C */)));});
      }
    };
    if(!E(_3o/* sd5B */)){
      return new F(function(){return _3v/* sd5M */(E(_2P/* Haste.Ajax.$fToAnyMethod2 */));});
    }else{
      return new F(function(){return _3v/* sd5M */(E(_2O/* Haste.Ajax.$fToAnyMethod1 */));});
    }
  };
  return new F(function(){return A2(_3f/* Control.Monad.IO.Class.liftIO */,_3k/* sd5x */, _3u/* sd70 */);});
},
_3M/* pageTabGroup27 */ = 400,
_3N/* pageTabGroup26 */ = new T2(1,_3M/* Page.pageTabGroup27 */,_I/* GHC.Types.[] */),
_3O/* pageTabGroup25 */ = new T2(1,_3N/* Page.pageTabGroup26 */,_2H/* Page.pageTabGroup10 */),
_3P/* pageTabGroup24 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_3O/* Page.pageTabGroup25 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_3Q/* pageTabGroup23 */ = new T2(7,_3P/* Page.pageTabGroup24 */,_I/* GHC.Types.[] */),
_3R/* dataTab */ = new T3(0,_3Q/* Page.pageTabGroup23 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_3S/* getRadioValue_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.val(); })");
}),
_3T/* getRespondentKey2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#respondent_key_field"));
}),
_3U/* pageTabGroup32 */ = 300,
_3V/* pageTabGroup31 */ = new T2(1,_3U/* Page.pageTabGroup32 */,_I/* GHC.Types.[] */),
_3W/* pageTabGroup30 */ = new T2(1,_3V/* Page.pageTabGroup31 */,_2H/* Page.pageTabGroup10 */),
_3X/* pageTabGroup29 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_3W/* Page.pageTabGroup30 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_3Y/* pageTabGroup28 */ = new T2(7,_3X/* Page.pageTabGroup29 */,_I/* GHC.Types.[] */),
_3Z/* lifecycleTab */ = new T3(0,_3Y/* Page.pageTabGroup28 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_40/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getData"));
}),
_41/* lvl12 */ = "respondent_key",
_42/* appearJq5 */ = "(function (key, val, jq) { jq.css(key, val); return jq; })",
_43/* $wa2 */ = function(_44/* stVA */, _45/* stVB */, _46/* stVC */, _/* EXTERNAL */){
  var _47/* stVR */ = eval/* EXTERNAL */(E(_42/* FormEngine.JQuery.appearJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_47/* stVR */), toJSStr/* EXTERNAL */(E(_44/* stVA */)), toJSStr/* EXTERNAL */(E(_45/* stVB */)), _46/* stVC */);});
},
_48/* itos */ = function(_49/* sfbi */, _4a/* sfbj */){
  var _4b/* sfbl */ = jsShowI/* EXTERNAL */(_49/* sfbi */);
  return new F(function(){return _12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_4b/* sfbl */), _4a/* sfbj */);});
},
_4c/* shows7 */ = 41,
_4d/* shows8 */ = 40,
_4e/* $wshowSignedInt */ = function(_4f/* sfbq */, _4g/* sfbr */, _4h/* sfbs */){
  if(_4g/* sfbr */>=0){
    return new F(function(){return _48/* GHC.Show.itos */(_4g/* sfbr */, _4h/* sfbs */);});
  }else{
    if(_4f/* sfbq */<=6){
      return new F(function(){return _48/* GHC.Show.itos */(_4g/* sfbr */, _4h/* sfbs */);});
    }else{
      return new T2(1,_4d/* GHC.Show.shows8 */,new T(function(){
        var _4i/* sfby */ = jsShowI/* EXTERNAL */(_4g/* sfbr */);
        return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_4i/* sfby */), new T2(1,_4c/* GHC.Show.shows7 */,_4h/* sfbs */)));
      }));
    }
  }
},
_4j/* toPx1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("px"));
}),
_4k/* $wtoPx */ = function(_4l/* strJ */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(0, _4l/* strJ */, _I/* GHC.Types.[] */)), _4j/* FormEngine.JQuery.toPx1 */);});
},
_4m/* descSubpaneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane"));
}),
_4n/* elemChapter */ = function(_4o/* s6NU */){
  while(1){
    var _4p/* s6NV */ = E(_4o/* s6NU */);
    switch(_4p/* s6NV */._){
      case 0:
        return E(_4p/* s6NV */);
      case 1:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 2:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 3:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 4:
        _4o/* s6NU */ = _4p/* s6NV */.e;
        continue;
      case 5:
        _4o/* s6NU */ = _4p/* s6NV */.b;
        continue;
      case 6:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 7:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 8:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 9:
        _4o/* s6NU */ = _4p/* s6NV */.e;
        continue;
      case 10:
        _4o/* s6NU */ = _4p/* s6NV */.d;
        continue;
      case 11:
        _4o/* s6NU */ = _4p/* s6NV */.b;
        continue;
      default:
        _4o/* s6NU */ = _4p/* s6NV */.b;
        continue;
    }
  }
},
_4q/* elementId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_G"));
}),
_4r/* fiDescriptor */ = function(_4s/* s5sB */){
  var _4t/* s5sC */ = E(_4s/* s5sB */);
  switch(_4t/* s5sC */._){
    case 0:
      return E(_4t/* s5sC */.a);
    case 1:
      return E(_4t/* s5sC */.a);
    case 2:
      return E(_4t/* s5sC */.a);
    case 3:
      return E(_4t/* s5sC */.a);
    case 4:
      return E(_4t/* s5sC */.a);
    case 5:
      return E(_4t/* s5sC */.a);
    case 6:
      return E(_4t/* s5sC */.a);
    case 7:
      return E(_4t/* s5sC */.a);
    case 8:
      return E(_4t/* s5sC */.a);
    case 9:
      return E(_4t/* s5sC */.a);
    case 10:
      return E(_4t/* s5sC */.a);
    case 11:
      return E(_4t/* s5sC */.a);
    default:
      return E(_4t/* s5sC */.a);
  }
},
_4u/* formItem */ = function(_4v/* s6F4 */){
  var _4w/* s6F5 */ = E(_4v/* s6F4 */);
  switch(_4w/* s6F5 */._){
    case 0:
      return E(_4w/* s6F5 */.a);
    case 1:
      return E(_4w/* s6F5 */.a);
    case 2:
      return E(_4w/* s6F5 */.a);
    case 3:
      return E(_4w/* s6F5 */.a);
    case 4:
      return E(_4w/* s6F5 */.a);
    case 5:
      return E(_4w/* s6F5 */.a);
    case 6:
      return E(_4w/* s6F5 */.a);
    case 7:
      return E(_4w/* s6F5 */.a);
    case 8:
      return E(_4w/* s6F5 */.a);
    case 9:
      return E(_4w/* s6F5 */.a);
    case 10:
      return E(_4w/* s6F5 */.a);
    case 11:
      return E(_4w/* s6F5 */.a);
    default:
      return E(_4w/* s6F5 */.a);
  }
},
_4x/* groupNo */ = function(_4y/* s6FR */){
  var _4z/* s6FS */ = E(_4y/* s6FR */);
  switch(_4z/* s6FS */._){
    case 1:
      return E(_4z/* s6FS */.c);
    case 2:
      return E(_4z/* s6FS */.c);
    case 3:
      return E(_4z/* s6FS */.c);
    case 4:
      return E(_4z/* s6FS */.d);
    case 6:
      return E(_4z/* s6FS */.c);
    case 7:
      return E(_4z/* s6FS */.c);
    case 8:
      return E(_4z/* s6FS */.c);
    case 9:
      return E(_4z/* s6FS */.d);
    case 10:
      return E(_4z/* s6FS */.c);
    default:
      return __Z/* EXTERNAL */;
  }
},
_4A/* $fShowInt_$cshow */ = function(_4B/* sffD */){
  return new F(function(){return _4e/* GHC.Show.$wshowSignedInt */(0, E(_4B/* sffD */), _I/* GHC.Types.[] */);});
},
_4C/* $wgo */ = function(_4D/* s5tJ */, _4E/* s5tK */){
  var _4F/* s5tL */ = E(_4D/* s5tJ */);
  if(!_4F/* s5tL */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4G/* s5tM */ = _4F/* s5tL */.a,
    _4H/* s5tO */ = E(_4E/* s5tK */);
    return (_4H/* s5tO */==1) ? new T2(1,new T(function(){
      return B(_4A/* GHC.Show.$fShowInt_$cshow */(_4G/* s5tM */));
    }),_I/* GHC.Types.[] */) : new T2(1,new T(function(){
      return B(_4A/* GHC.Show.$fShowInt_$cshow */(_4G/* s5tM */));
    }),new T(function(){
      return B(_4C/* FormEngine.FormItem.$wgo */(_4F/* s5tL */.b, _4H/* s5tO */-1|0));
    }));
  }
},
_4I/* intercalate1 */ = function(_4J/* s1WJa */){
  var _4K/* s1WJb */ = E(_4J/* s1WJa */);
  if(!_4K/* s1WJb */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _12/* GHC.Base.++ */(_4K/* s1WJb */.a, new T(function(){
      return B(_4I/* Data.OldList.intercalate1 */(_4K/* s1WJb */.b));
    },1));});
  }
},
_4L/* numbering2text1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_4M/* prependToAll */ = function(_4N/* s1WIX */, _4O/* s1WIY */){
  var _4P/* s1WIZ */ = E(_4O/* s1WIY */);
  return (_4P/* s1WIZ */._==0) ? __Z/* EXTERNAL */ : new T2(1,_4N/* s1WIX */,new T2(1,_4P/* s1WIZ */.a,new T(function(){
    return B(_4M/* Data.OldList.prependToAll */(_4N/* s1WIX */, _4P/* s1WIZ */.b));
  })));
},
_4Q/* numbering2text */ = function(_4R/* s5tT */){
  var _4S/* s5tU */ = E(_4R/* s5tT */);
  if(!_4S/* s5tU */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4T/* s5tZ */ = E(_4S/* s5tU */.b)+1|0;
    if(0>=_4T/* s5tZ */){
      return __Z/* EXTERNAL */;
    }else{
      var _4U/* s5u2 */ = B(_4C/* FormEngine.FormItem.$wgo */(_4S/* s5tU */.a, _4T/* s5tZ */));
      if(!_4U/* s5u2 */._){
        return __Z/* EXTERNAL */;
      }else{
        return new F(function(){return _4I/* Data.OldList.intercalate1 */(new T2(1,_4U/* s5u2 */.a,new T(function(){
          return B(_4M/* Data.OldList.prependToAll */(_4L/* FormEngine.FormItem.numbering2text1 */, _4U/* s5u2 */.b));
        })));});
      }
    }
  }
},
_4V/* elementId */ = function(_4W/* s6Gv */){
  var _4X/* s6Gw */ = B(_4x/* FormEngine.FormElement.FormElement.groupNo */(_4W/* s6Gv */));
  if(!_4X/* s6Gw */._){
    return new F(function(){return _4Q/* FormEngine.FormItem.numbering2text */(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_4W/* s6Gv */)))).b);});
  }else{
    var _4Y/* s6GY */ = new T(function(){
      return B(_12/* GHC.Base.++ */(_4q/* FormEngine.FormElement.FormElement.elementId1 */, new T(function(){
        return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_4X/* s6Gw */.a), _I/* GHC.Types.[] */));
      },1)));
    },1);
    return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_4W/* s6Gv */)))).b)), _4Y/* s6GY */);});
  }
},
_4Z/* getScrollTop_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.scrollTop(); })");
}),
_50/* getTop_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.position().top; })");
}),
_51/* getWindow_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function () { return $(window); })");
}),
_52/* isVisible_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.is(\':visible\'); })");
}),
_53/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_54/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_55/* select2 */ = "(function (elId) { var res = $(elId); if (res.length === 0) { console.warn(\'empty $ selection \' + elId); }; return res; })",
_56/* select1 */ = function(_57/* stNO */, _/* EXTERNAL */){
  var _58/* stNY */ = eval/* EXTERNAL */(E(_55/* FormEngine.JQuery.select2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_58/* stNY */), toJSStr/* EXTERNAL */(E(_57/* stNO */)));});
},
_59/* $wa1 */ = function(_5a/* sq8T */, _/* EXTERNAL */){
  var _5b/* sq8V */ = E(_5a/* sq8T */);
  if(!_5b/* sq8V */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _5c/* sq8Y */ = B(_12/* GHC.Base.++ */(_54/* Main.lvl2 */, new T(function(){
      return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_5b/* sq8V */.a)))), _4m/* FormEngine.FormElement.Identifiers.descSubpaneId1 */));
    },1))),
    _5d/* sq92 */ = B(_56/* FormEngine.JQuery.select1 */(_5c/* sq8Y */, _/* EXTERNAL */)),
    _5e/* sq97 */ = E(_52/* FormEngine.JQuery.isVisible_f1 */),
    _5f/* sq9a */ = __app1/* EXTERNAL */(_5e/* sq97 */, E(_5d/* sq92 */)),
    _5g/* sq9d */ = function(_5h/* sq9e */, _/* EXTERNAL */){
      var _5i/* sq9g */ = E(_5h/* sq9e */);
      if(!_5i/* sq9g */._){
        return _I/* GHC.Types.[] */;
      }else{
        var _5j/* sq9j */ = B(_12/* GHC.Base.++ */(_54/* Main.lvl2 */, new T(function(){
          return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_5i/* sq9g */.a)))), _4m/* FormEngine.FormElement.Identifiers.descSubpaneId1 */));
        },1))),
        _5k/* sq9n */ = B(_56/* FormEngine.JQuery.select1 */(_5j/* sq9j */, _/* EXTERNAL */)),
        _5l/* sq9t */ = __app1/* EXTERNAL */(_5e/* sq97 */, E(_5k/* sq9n */)),
        _5m/* sq9w */ = B(_5g/* sq9d */(_5i/* sq9g */.b, _/* EXTERNAL */));
        return new T(function(){
          if(!_5l/* sq9t */){
            return E(_5m/* sq9w */);
          }else{
            return new T2(1,_5j/* sq9j */,_5m/* sq9w */);
          }
        });
      }
    },
    _5n/* sq9B */ = B(_5g/* sq9d */(_5b/* sq8V */.b, _/* EXTERNAL */)),
    _5o/* sq9E */ = function(_5p/* sq9F */, _5q/* sq9G */){
      var _5r/* sq9H */ = B(_56/* FormEngine.JQuery.select1 */(_5p/* sq9F */, _/* EXTERNAL */)),
      _5s/* sq9N */ = __app0/* EXTERNAL */(E(_51/* FormEngine.JQuery.getWindow_f1 */)),
      _5t/* sq9T */ = __app1/* EXTERNAL */(E(_4Z/* FormEngine.JQuery.getScrollTop_f1 */), _5s/* sq9N */),
      _5u/* sq9W */ = E(_5r/* sq9H */),
      _5v/* sqa1 */ = __app1/* EXTERNAL */(E(_50/* FormEngine.JQuery.getTop_f1 */), _5u/* sq9W */),
      _5w/* sqa5 */ = Number/* EXTERNAL */(_5t/* sq9T */),
      _5x/* sqa9 */ = jsTrunc/* EXTERNAL */(_5w/* sqa5 */),
      _5y/* sqad */ = Number/* EXTERNAL */(_5v/* sqa1 */),
      _5z/* sqah */ = jsTrunc/* EXTERNAL */(_5y/* sqad */),
      _5A/* sqak */ = _5x/* sqa9 */-_5z/* sqah */|0;
      if(_5A/* sqak */<=0){
        return _0/* GHC.Tuple.() */;
      }else{
        var _5B/* sqao */ = B(_43/* FormEngine.JQuery.$wa2 */(_53/* Main.lvl1 */, B(_4k/* FormEngine.JQuery.$wtoPx */(_5A/* sqak */)), _5u/* sq9W */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      }
    };
    if(!_5f/* sq9a */){
      var _5C/* sqas */ = E(_5n/* sq9B */);
      if(!_5C/* sqas */._){
        return _0/* GHC.Tuple.() */;
      }else{
        return new F(function(){return _5o/* sq9E */(_5C/* sqas */.a, _5C/* sqas */.b);});
      }
    }else{
      return new F(function(){return _5o/* sq9E */(_5c/* sq8Y */, _5n/* sq9B */);});
    }
  }
},
_5D/* resize2 */ = "(function (jq) { jq.resize(); })",
_5E/* $wa17 */ = function(_5F/* sttU */, _/* EXTERNAL */){
  var _5G/* sttZ */ = eval/* EXTERNAL */(E(_5D/* FormEngine.JQuery.resize2 */)),
  _5H/* stu7 */ = __app1/* EXTERNAL */(E(_5G/* sttZ */), _5F/* sttU */);
  return _5F/* sttU */;
},
_5I/* catMaybes1 */ = function(_5J/*  s7rA */){
  while(1){
    var _5K/*  catMaybes1 */ = B((function(_5L/* s7rA */){
      var _5M/* s7rB */ = E(_5L/* s7rA */);
      if(!_5M/* s7rB */._){
        return __Z/* EXTERNAL */;
      }else{
        var _5N/* s7rD */ = _5M/* s7rB */.b,
        _5O/* s7rE */ = E(_5M/* s7rB */.a);
        if(!_5O/* s7rE */._){
          _5J/*  s7rA */ = _5N/* s7rD */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_5O/* s7rE */.a,new T(function(){
            return B(_5I/* Data.Maybe.catMaybes1 */(_5N/* s7rD */));
          }));
        }
      }
    })(_5J/*  s7rA */));
    if(_5K/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _5K/*  catMaybes1 */;
    }
  }
},
_5P/* errorIO2 */ = "(function (s) { console.error(s); })",
_5Q/* errorIO1 */ = function(_5R/* stCy */, _/* EXTERNAL */){
  var _5S/* stCI */ = eval/* EXTERNAL */(E(_5P/* FormEngine.JQuery.errorIO2 */)),
  _5T/* stCQ */ = __app1/* EXTERNAL */(E(_5S/* stCI */), toJSStr/* EXTERNAL */(E(_5R/* stCy */)));
  return _0/* GHC.Tuple.() */;
},
_5U/* $fShowNumbering2 */ = 0,
_5V/* $wgo2 */ = function(_5W/*  s5mL */, _5X/*  s5mM */, _5Y/*  s5mN */){
  while(1){
    var _5Z/*  $wgo2 */ = B((function(_60/* s5mL */, _61/* s5mM */, _62/* s5mN */){
      var _63/* s5mO */ = E(_60/* s5mL */);
      if(!_63/* s5mO */._){
        return new T2(0,_61/* s5mM */,_62/* s5mN */);
      }else{
        var _64/* s5mP */ = _63/* s5mO */.a,
        _65/* s5n0 */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_62/* s5mN */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_61/* s5mM */, _64/* s5mP */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _5W/*  s5mL */ = _63/* s5mO */.b;
        _5X/*  s5mM */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_61/* s5mM */, _64/* s5mP */)).a);
        });
        _5Y/*  s5mN */ = _65/* s5n0 */;
        return __continue/* EXTERNAL */;
      }
    })(_5W/*  s5mL */, _5X/*  s5mM */, _5Y/*  s5mN */));
    if(_5Z/*  $wgo2 */!=__continue/* EXTERNAL */){
      return _5Z/*  $wgo2 */;
    }
  }
},
_67/* $wgo3 */ = function(_68/*  s5n1 */, _69/*  s5n2 */, _6a/*  s5n3 */){
  while(1){
    var _6b/*  $wgo3 */ = B((function(_6c/* s5n1 */, _6d/* s5n2 */, _6e/* s5n3 */){
      var _6f/* s5n4 */ = E(_6c/* s5n1 */);
      if(!_6f/* s5n4 */._){
        return new T2(0,_6d/* s5n2 */,_6e/* s5n3 */);
      }else{
        var _6g/* s5n5 */ = _6f/* s5n4 */.a,
        _6h/* s5ng */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6e/* s5n3 */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6d/* s5n2 */, _6g/* s5n5 */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _68/*  s5n1 */ = _6f/* s5n4 */.b;
        _69/*  s5n2 */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6d/* s5n2 */, _6g/* s5n5 */)).a);
        });
        _6a/*  s5n3 */ = _6h/* s5ng */;
        return __continue/* EXTERNAL */;
      }
    })(_68/*  s5n1 */, _69/*  s5n2 */, _6a/*  s5n3 */));
    if(_6b/*  $wgo3 */!=__continue/* EXTERNAL */){
      return _6b/*  $wgo3 */;
    }
  }
},
_6i/* $wgo4 */ = function(_6j/*  s5nh */, _6k/*  s5ni */, _6l/*  s5nj */){
  while(1){
    var _6m/*  $wgo4 */ = B((function(_6n/* s5nh */, _6o/* s5ni */, _6p/* s5nj */){
      var _6q/* s5nk */ = E(_6n/* s5nh */);
      if(!_6q/* s5nk */._){
        return new T2(0,_6o/* s5ni */,_6p/* s5nj */);
      }else{
        var _6r/* s5nl */ = _6q/* s5nk */.a,
        _6s/* s5nw */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6p/* s5nj */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6o/* s5ni */, _6r/* s5nl */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6j/*  s5nh */ = _6q/* s5nk */.b;
        _6k/*  s5ni */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6o/* s5ni */, _6r/* s5nl */)).a);
        });
        _6l/*  s5nj */ = _6s/* s5nw */;
        return __continue/* EXTERNAL */;
      }
    })(_6j/*  s5nh */, _6k/*  s5ni */, _6l/*  s5nj */));
    if(_6m/*  $wgo4 */!=__continue/* EXTERNAL */){
      return _6m/*  $wgo4 */;
    }
  }
},
_6t/* $wgo5 */ = function(_6u/*  s5nx */, _6v/*  s5ny */, _6w/*  s5nz */){
  while(1){
    var _6x/*  $wgo5 */ = B((function(_6y/* s5nx */, _6z/* s5ny */, _6A/* s5nz */){
      var _6B/* s5nA */ = E(_6y/* s5nx */);
      if(!_6B/* s5nA */._){
        return new T2(0,_6z/* s5ny */,_6A/* s5nz */);
      }else{
        var _6C/* s5nB */ = _6B/* s5nA */.a,
        _6D/* s5nM */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6A/* s5nz */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6z/* s5ny */, _6C/* s5nB */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6u/*  s5nx */ = _6B/* s5nA */.b;
        _6v/*  s5ny */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6z/* s5ny */, _6C/* s5nB */)).a);
        });
        _6w/*  s5nz */ = _6D/* s5nM */;
        return __continue/* EXTERNAL */;
      }
    })(_6u/*  s5nx */, _6v/*  s5ny */, _6w/*  s5nz */));
    if(_6x/*  $wgo5 */!=__continue/* EXTERNAL */){
      return _6x/*  $wgo5 */;
    }
  }
},
_6E/* $wgo6 */ = function(_6F/*  s5nN */, _6G/*  s5nO */, _6H/*  s5nP */){
  while(1){
    var _6I/*  $wgo6 */ = B((function(_6J/* s5nN */, _6K/* s5nO */, _6L/* s5nP */){
      var _6M/* s5nQ */ = E(_6J/* s5nN */);
      if(!_6M/* s5nQ */._){
        return new T2(0,_6K/* s5nO */,_6L/* s5nP */);
      }else{
        var _6N/* s5nR */ = _6M/* s5nQ */.a,
        _6O/* s5o2 */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6L/* s5nP */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6K/* s5nO */, _6N/* s5nR */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6F/*  s5nN */ = _6M/* s5nQ */.b;
        _6G/*  s5nO */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_6K/* s5nO */, _6N/* s5nR */)).a);
        });
        _6H/*  s5nP */ = _6O/* s5o2 */;
        return __continue/* EXTERNAL */;
      }
    })(_6F/*  s5nN */, _6G/*  s5nO */, _6H/*  s5nP */));
    if(_6I/*  $wgo6 */!=__continue/* EXTERNAL */){
      return _6I/*  $wgo6 */;
    }
  }
},
_6P/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_6Q/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_6R/* lvl2 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_6Q/* GHC.List.prel_list_str */, _6P/* GHC.List.lvl1 */));
}),
_6S/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_6R/* GHC.List.lvl2 */));
}),
_6T/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_6U/* lvl4 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_6Q/* GHC.List.prel_list_str */, _6T/* GHC.List.lvl3 */));
}),
_6V/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_6U/* GHC.List.lvl4 */));
}),
_6W/* poly_$wgo2 */ = function(_6X/* s9uh */, _6Y/* s9ui */){
  while(1){
    var _6Z/* s9uj */ = E(_6X/* s9uh */);
    if(!_6Z/* s9uj */._){
      return E(_6V/* GHC.List.!!1 */);
    }else{
      var _70/* s9um */ = E(_6Y/* s9ui */);
      if(!_70/* s9um */){
        return E(_6Z/* s9uj */.a);
      }else{
        _6X/* s9uh */ = _6Z/* s9uj */.b;
        _6Y/* s9ui */ = _70/* s9um */-1|0;
        continue;
      }
    }
  }
},
_71/* $w!! */ = function(_72/* s9uo */, _73/* s9up */){
  if(_73/* s9up */>=0){
    return new F(function(){return _6W/* GHC.List.poly_$wgo2 */(_72/* s9uo */, _73/* s9up */);});
  }else{
    return E(_6S/* GHC.List.negIndex */);
  }
},
_74/* xs */ = new T(function(){
  return new T2(1,_5U/* FormEngine.FormItem.$fShowNumbering2 */,_74/* FormEngine.FormItem.xs */);
}),
_75/* incrementAtLevel */ = function(_76/* s5mo */){
  var _77/* s5mp */ = E(_76/* s5mo */);
  if(!_77/* s5mp */._){
    return __Z/* EXTERNAL */;
  }else{
    var _78/* s5mq */ = _77/* s5mp */.a,
    _79/* s5mr */ = _77/* s5mp */.b,
    _7a/* s5mK */ = new T(function(){
      var _7b/* s5ms */ = E(_79/* s5mr */),
      _7c/* s5my */ = new T2(1,new T(function(){
        return B(_71/* GHC.List.$w!! */(_78/* s5mq */, _7b/* s5ms */))+1|0;
      }),_74/* FormEngine.FormItem.xs */);
      if(0>=_7b/* s5ms */){
        return E(_7c/* s5my */);
      }else{
        var _7d/* s5mB */ = function(_7e/* s5mC */, _7f/* s5mD */){
          var _7g/* s5mE */ = E(_7e/* s5mC */);
          if(!_7g/* s5mE */._){
            return E(_7c/* s5my */);
          }else{
            var _7h/* s5mF */ = _7g/* s5mE */.a,
            _7i/* s5mH */ = E(_7f/* s5mD */);
            return (_7i/* s5mH */==1) ? new T2(1,_7h/* s5mF */,_7c/* s5my */) : new T2(1,_7h/* s5mF */,new T(function(){
              return B(_7d/* s5mB */(_7g/* s5mE */.b, _7i/* s5mH */-1|0));
            }));
          }
        };
        return B(_7d/* s5mB */(_78/* s5mq */, _7b/* s5ms */));
      }
    });
    return new T2(1,_7a/* s5mK */,_79/* s5mr */);
  }
},
_7j/* $wgo7 */ = function(_7k/*  s5o3 */, _7l/*  s5o4 */, _7m/*  s5o5 */){
  while(1){
    var _7n/*  $wgo7 */ = B((function(_7o/* s5o3 */, _7p/* s5o4 */, _7q/* s5o5 */){
      var _7r/* s5o6 */ = E(_7o/* s5o3 */);
      if(!_7r/* s5o6 */._){
        return new T2(0,_7p/* s5o4 */,_7q/* s5o5 */);
      }else{
        var _7s/* s5o8 */ = _7r/* s5o6 */.b,
        _7t/* s5o9 */ = E(_7r/* s5o6 */.a);
        if(!_7t/* s5o9 */._){
          var _7u/*   s5o4 */ = _7p/* s5o4 */;
          _7k/*  s5o3 */ = _7s/* s5o8 */;
          _7l/*  s5o4 */ = _7u/*   s5o4 */;
          _7m/*  s5o5 */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_7q/* s5o5 */, new T2(1,_7t/* s5o9 */,_I/* GHC.Types.[] */)));
          });
          return __continue/* EXTERNAL */;
        }else{
          var _7v/* s5ov */ = new T(function(){
            var _7w/* s5os */ = new T(function(){
              var _7x/* s5oo */ = new T(function(){
                var _7y/* s5oh */ = E(_7p/* s5o4 */);
                if(!_7y/* s5oh */._){
                  return __Z/* EXTERNAL */;
                }else{
                  return new T2(1,_7y/* s5oh */.a,new T(function(){
                    return E(_7y/* s5oh */.b)+1|0;
                  }));
                }
              });
              return E(B(_6E/* FormEngine.FormItem.$wgo6 */(_7t/* s5o9 */.c, _7x/* s5oo */, _I/* GHC.Types.[] */)).b);
            });
            return B(_12/* GHC.Base.++ */(_7q/* s5o5 */, new T2(1,new T3(1,_7p/* s5o4 */,_7t/* s5o9 */.b,_7w/* s5os */),_I/* GHC.Types.[] */)));
          });
          _7k/*  s5o3 */ = _7s/* s5o8 */;
          _7l/*  s5o4 */ = new T(function(){
            return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7p/* s5o4 */));
          });
          _7m/*  s5o5 */ = _7v/* s5ov */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_7k/*  s5o3 */, _7l/*  s5o4 */, _7m/*  s5o5 */));
    if(_7n/*  $wgo7 */!=__continue/* EXTERNAL */){
      return _7n/*  $wgo7 */;
    }
  }
},
_66/* $wincrementNumbering */ = function(_7z/* s5ow */, _7A/* s5ox */){
  var _7B/* s5oy */ = E(_7A/* s5ox */);
  switch(_7B/* s5oy */._){
    case 0:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T1(0,new T(function(){
        var _7C/* s5oB */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7C/* s5oB */.a,b:_7z/* s5ow */,c:_7C/* s5oB */.c,d:_7C/* s5oB */.d,e:_7C/* s5oB */.e,f:_7C/* s5oB */.f,g:_7C/* s5oB */.g,h:_7C/* s5oB */.h,i:_7C/* s5oB */.i};
      })));
    case 1:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T1(1,new T(function(){
        var _7D/* s5oP */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7D/* s5oP */.a,b:_7z/* s5ow */,c:_7D/* s5oP */.c,d:_7D/* s5oP */.d,e:_7D/* s5oP */.e,f:_7D/* s5oP */.f,g:_7D/* s5oP */.g,h:_7D/* s5oP */.h,i:_7D/* s5oP */.i};
      })));
    case 2:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T1(2,new T(function(){
        var _7E/* s5p3 */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7E/* s5p3 */.a,b:_7z/* s5ow */,c:_7E/* s5p3 */.c,d:_7E/* s5p3 */.d,e:_7E/* s5p3 */.e,f:_7E/* s5p3 */.f,g:_7E/* s5p3 */.g,h:_7E/* s5p3 */.h,i:_7E/* s5p3 */.i};
      })));
    case 3:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T2(3,new T(function(){
        var _7F/* s5pi */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7F/* s5pi */.a,b:_7z/* s5ow */,c:_7F/* s5pi */.c,d:_7F/* s5pi */.d,e:_7F/* s5pi */.e,f:_7F/* s5pi */.f,g:_7F/* s5pi */.g,h:_7F/* s5pi */.h,i:_7F/* s5pi */.i};
      }),_7B/* s5oy */.b));
    case 4:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T2(4,new T(function(){
        var _7G/* s5px */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7G/* s5px */.a,b:_7z/* s5ow */,c:_7G/* s5px */.c,d:_7G/* s5px */.d,e:_7G/* s5px */.e,f:_7G/* s5px */.f,g:_7G/* s5px */.g,h:_7G/* s5px */.h,i:_7G/* s5px */.i};
      }),_7B/* s5oy */.b));
    case 5:
      var _7H/* s5q8 */ = new T(function(){
        var _7I/* s5q4 */ = new T(function(){
          var _7J/* s5pX */ = E(_7z/* s5ow */);
          if(!_7J/* s5pX */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7J/* s5pX */.a,new T(function(){
              return E(_7J/* s5pX */.b)+1|0;
            }));
          }
        });
        return E(B(_7j/* FormEngine.FormItem.$wgo7 */(_7B/* s5oy */.b, _7I/* s5q4 */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T2(5,new T(function(){
        var _7K/* s5pM */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7K/* s5pM */.a,b:_7z/* s5ow */,c:_7K/* s5pM */.c,d:_7K/* s5pM */.d,e:_7K/* s5pM */.e,f:_7K/* s5pM */.f,g:_7K/* s5pM */.g,h:_7K/* s5pM */.h,i:_7K/* s5pM */.i};
      }),_7H/* s5q8 */));
    case 6:
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T2(6,new T(function(){
        var _7L/* s5qd */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7L/* s5qd */.a,b:_7z/* s5ow */,c:_7L/* s5qd */.c,d:_7L/* s5qd */.d,e:_7L/* s5qd */.e,f:_7L/* s5qd */.f,g:_7L/* s5qd */.g,h:_7L/* s5qd */.h,i:_7L/* s5qd */.i};
      }),_7B/* s5oy */.b));
    case 7:
      var _7M/* s5qO */ = new T(function(){
        var _7N/* s5qK */ = new T(function(){
          var _7O/* s5qD */ = E(_7z/* s5ow */);
          if(!_7O/* s5qD */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7O/* s5qD */.a,new T(function(){
              return E(_7O/* s5qD */.b)+1|0;
            }));
          }
        });
        return E(B(_6t/* FormEngine.FormItem.$wgo5 */(_7B/* s5oy */.b, _7N/* s5qK */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T2(7,new T(function(){
        var _7P/* s5qs */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7P/* s5qs */.a,b:_7z/* s5ow */,c:_7P/* s5qs */.c,d:_7P/* s5qs */.d,e:_7P/* s5qs */.e,f:_7P/* s5qs */.f,g:_7P/* s5qs */.g,h:_7P/* s5qs */.h,i:_7P/* s5qs */.i};
      }),_7M/* s5qO */));
    case 8:
      var _7Q/* s5rk */ = new T(function(){
        var _7R/* s5rg */ = new T(function(){
          var _7S/* s5r9 */ = E(_7z/* s5ow */);
          if(!_7S/* s5r9 */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7S/* s5r9 */.a,new T(function(){
              return E(_7S/* s5r9 */.b)+1|0;
            }));
          }
        });
        return E(B(_6i/* FormEngine.FormItem.$wgo4 */(_7B/* s5oy */.c, _7R/* s5rg */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T3(8,new T(function(){
        var _7T/* s5qU */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7T/* s5qU */.a,b:_7z/* s5ow */,c:_7T/* s5qU */.c,d:_7T/* s5qU */.d,e:_7T/* s5qU */.e,f:_7T/* s5qU */.f,g:_7T/* s5qU */.g,h:_7T/* s5qU */.h,i:_7T/* s5qU */.i};
      }),new T(function(){
        var _7U/* s5r5 */ = E(_7z/* s5ow */);
        if(!_7U/* s5r5 */._){
          return E(_5U/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_7U/* s5r5 */.b);
        }
      }),_7Q/* s5rk */));
    case 9:
      var _7V/* s5rQ */ = new T(function(){
        var _7W/* s5rM */ = new T(function(){
          var _7X/* s5rF */ = E(_7z/* s5ow */);
          if(!_7X/* s5rF */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7X/* s5rF */.a,new T(function(){
              return E(_7X/* s5rF */.b)+1|0;
            }));
          }
        });
        return E(B(_67/* FormEngine.FormItem.$wgo3 */(_7B/* s5oy */.c, _7W/* s5rM */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T3(9,new T(function(){
        var _7Y/* s5rq */ = E(_7B/* s5oy */.a);
        return {_:0,a:_7Y/* s5rq */.a,b:_7z/* s5ow */,c:_7Y/* s5rq */.c,d:_7Y/* s5rq */.d,e:_7Y/* s5rq */.e,f:_7Y/* s5rq */.f,g:_7Y/* s5rq */.g,h:_7Y/* s5rq */.h,i:_7Y/* s5rq */.i};
      }),new T(function(){
        var _7Z/* s5rB */ = E(_7z/* s5ow */);
        if(!_7Z/* s5rB */._){
          return E(_5U/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_7Z/* s5rB */.b);
        }
      }),_7V/* s5rQ */));
    case 10:
      var _80/* s5sm */ = new T(function(){
        var _81/* s5si */ = new T(function(){
          var _82/* s5sb */ = E(_7z/* s5ow */);
          if(!_82/* s5sb */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_82/* s5sb */.a,new T(function(){
              return E(_82/* s5sb */.b)+1|0;
            }));
          }
        });
        return E(B(_5V/* FormEngine.FormItem.$wgo2 */(_7B/* s5oy */.c, _81/* s5si */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_75/* FormEngine.FormItem.incrementAtLevel */(_7z/* s5ow */));
      }),new T3(10,new T(function(){
        var _83/* s5rW */ = E(_7B/* s5oy */.a);
        return {_:0,a:_83/* s5rW */.a,b:_7z/* s5ow */,c:_83/* s5rW */.c,d:_83/* s5rW */.d,e:_83/* s5rW */.e,f:_83/* s5rW */.f,g:_83/* s5rW */.g,h:_83/* s5rW */.h,i:_83/* s5rW */.i};
      }),new T(function(){
        var _84/* s5s7 */ = E(_7z/* s5ow */);
        if(!_84/* s5s7 */._){
          return E(_5U/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_84/* s5s7 */.b);
        }
      }),_80/* s5sm */));
    default:
      return new T2(0,_7z/* s5ow */,_7B/* s5oy */);
  }
},
_85/* $wgo1 */ = function(_86/*  s5uA */, _87/*  s5uB */, _88/*  s5uC */){
  while(1){
    var _89/*  $wgo1 */ = B((function(_8a/* s5uA */, _8b/* s5uB */, _8c/* s5uC */){
      var _8d/* s5uD */ = E(_8a/* s5uA */);
      if(!_8d/* s5uD */._){
        return new T2(0,_8b/* s5uB */,_8c/* s5uC */);
      }else{
        var _8e/* s5uE */ = _8d/* s5uD */.a,
        _8f/* s5uP */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_8c/* s5uC */, new T2(1,new T(function(){
            return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_8b/* s5uB */, _8e/* s5uE */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _86/*  s5uA */ = _8d/* s5uD */.b;
        _87/*  s5uB */ = new T(function(){
          return E(B(_66/* FormEngine.FormItem.$wincrementNumbering */(_8b/* s5uB */, _8e/* s5uE */)).a);
        });
        _88/*  s5uC */ = _8f/* s5uP */;
        return __continue/* EXTERNAL */;
      }
    })(_86/*  s5uA */, _87/*  s5uB */, _88/*  s5uC */));
    if(_89/*  $wgo1 */!=__continue/* EXTERNAL */){
      return _89/*  $wgo1 */;
    }
  }
},
_8g/* NoNumbering */ = __Z/* EXTERNAL */,
_8h/* remark5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Your comments"));
}),
_8i/* remark4 */ = new T1(1,_8h/* FormStructure.Common.remark5 */),
_8j/* remark3 */ = {_:0,a:_8i/* FormStructure.Common.remark4 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_8k/* remark2 */ = new T1(1,_8j/* FormStructure.Common.remark3 */),
_8l/* remark1 */ = new T2(1,_8k/* FormStructure.Common.remark2 */,_I/* GHC.Types.[] */),
_8m/* remark6 */ = 0,
_8n/* True */ = true,
_8o/* remark9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Other"));
}),
_8p/* remark8 */ = new T1(1,_8o/* FormStructure.Common.remark9 */),
_8q/* remark7 */ = {_:0,a:_8p/* FormStructure.Common.remark8 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8r/* remark */ = new T3(8,_8q/* FormStructure.Common.remark7 */,_8m/* FormStructure.Common.remark6 */,_8l/* FormStructure.Common.remark1 */),
_8s/* ch0GeneralInformation3 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_8t/* ch0GeneralInformation37 */ = 0,
_8u/* ch0GeneralInformation40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Affiliation"));
}),
_8v/* ch0GeneralInformation39 */ = new T1(1,_8u/* FormStructure.Chapter0.ch0GeneralInformation40 */),
_8w/* ch0GeneralInformation38 */ = {_:0,a:_8v/* FormStructure.Chapter0.ch0GeneralInformation39 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8x/* ch0GeneralInformation36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Country"));
}),
_8y/* ch0GeneralInformation35 */ = new T1(1,_8x/* FormStructure.Chapter0.ch0GeneralInformation36 */),
_8z/* ch0GeneralInformation34 */ = {_:0,a:_8y/* FormStructure.Chapter0.ch0GeneralInformation35 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8A/* countries770 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("France"));
}),
_8B/* countries771 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FR"));
}),
_8C/* countries769 */ = new T2(0,_8B/* Countries.countries771 */,_8A/* Countries.countries770 */),
_8D/* countries767 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Guiana"));
}),
_8E/* countries768 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GF"));
}),
_8F/* countries766 */ = new T2(0,_8E/* Countries.countries768 */,_8D/* Countries.countries767 */),
_8G/* countries764 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Polynesia"));
}),
_8H/* countries765 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PF"));
}),
_8I/* countries763 */ = new T2(0,_8H/* Countries.countries765 */,_8G/* Countries.countries764 */),
_8J/* countries761 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Southern Territories"));
}),
_8K/* countries762 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TF"));
}),
_8L/* countries760 */ = new T2(0,_8K/* Countries.countries762 */,_8J/* Countries.countries761 */),
_8M/* countries758 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gabon"));
}),
_8N/* countries759 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GA"));
}),
_8O/* countries757 */ = new T2(0,_8N/* Countries.countries759 */,_8M/* Countries.countries758 */),
_8P/* countries755 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gambia"));
}),
_8Q/* countries756 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GM"));
}),
_8R/* countries754 */ = new T2(0,_8Q/* Countries.countries756 */,_8P/* Countries.countries755 */),
_8S/* countries752 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Georgia"));
}),
_8T/* countries753 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GE"));
}),
_8U/* countries751 */ = new T2(0,_8T/* Countries.countries753 */,_8S/* Countries.countries752 */),
_8V/* countries749 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Germany"));
}),
_8W/* countries750 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DE"));
}),
_8X/* countries748 */ = new T2(0,_8W/* Countries.countries750 */,_8V/* Countries.countries749 */),
_8Y/* countries746 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ghana"));
}),
_8Z/* countries747 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GH"));
}),
_90/* countries745 */ = new T2(0,_8Z/* Countries.countries747 */,_8Y/* Countries.countries746 */),
_91/* countries743 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gibraltar"));
}),
_92/* countries744 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GI"));
}),
_93/* countries742 */ = new T2(0,_92/* Countries.countries744 */,_91/* Countries.countries743 */),
_94/* countries740 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greece"));
}),
_95/* countries741 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GR"));
}),
_96/* countries739 */ = new T2(0,_95/* Countries.countries741 */,_94/* Countries.countries740 */),
_97/* countries737 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greenland"));
}),
_98/* countries738 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GL"));
}),
_99/* countries736 */ = new T2(0,_98/* Countries.countries738 */,_97/* Countries.countries737 */),
_9a/* countries734 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grenada"));
}),
_9b/* countries735 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GD"));
}),
_9c/* countries733 */ = new T2(0,_9b/* Countries.countries735 */,_9a/* Countries.countries734 */),
_9d/* countries731 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guadeloupe"));
}),
_9e/* countries732 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GP"));
}),
_9f/* countries730 */ = new T2(0,_9e/* Countries.countries732 */,_9d/* Countries.countries731 */),
_9g/* countries728 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guam"));
}),
_9h/* countries729 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GU"));
}),
_9i/* countries727 */ = new T2(0,_9h/* Countries.countries729 */,_9g/* Countries.countries728 */),
_9j/* countries725 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guatemala"));
}),
_9k/* countries726 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GT"));
}),
_9l/* countries724 */ = new T2(0,_9k/* Countries.countries726 */,_9j/* Countries.countries725 */),
_9m/* countries722 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guernsey"));
}),
_9n/* countries723 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GG"));
}),
_9o/* countries721 */ = new T2(0,_9n/* Countries.countries723 */,_9m/* Countries.countries722 */),
_9p/* countries719 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea"));
}),
_9q/* countries720 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GN"));
}),
_9r/* countries718 */ = new T2(0,_9q/* Countries.countries720 */,_9p/* Countries.countries719 */),
_9s/* countries716 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea-Bissau"));
}),
_9t/* countries717 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GW"));
}),
_9u/* countries715 */ = new T2(0,_9t/* Countries.countries717 */,_9s/* Countries.countries716 */),
_9v/* countries713 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guyana"));
}),
_9w/* countries714 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GY"));
}),
_9x/* countries712 */ = new T2(0,_9w/* Countries.countries714 */,_9v/* Countries.countries713 */),
_9y/* countries710 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haiti"));
}),
_9z/* countries711 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_9A/* countries709 */ = new T2(0,_9z/* Countries.countries711 */,_9y/* Countries.countries710 */),
_9B/* countries707 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Heard Island and McDonald Islands"));
}),
_9C/* countries708 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HM"));
}),
_9D/* countries706 */ = new T2(0,_9C/* Countries.countries708 */,_9B/* Countries.countries707 */),
_9E/* countries704 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Holy See (Vatican City State)"));
}),
_9F/* countries705 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VA"));
}),
_9G/* countries703 */ = new T2(0,_9F/* Countries.countries705 */,_9E/* Countries.countries704 */),
_9H/* countries251 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zimbabwe"));
}),
_9I/* countries252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZW"));
}),
_9J/* countries250 */ = new T2(0,_9I/* Countries.countries252 */,_9H/* Countries.countries251 */),
_9K/* countries249 */ = new T2(1,_9J/* Countries.countries250 */,_I/* GHC.Types.[] */),
_9L/* countries254 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zambia"));
}),
_9M/* countries255 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZM"));
}),
_9N/* countries253 */ = new T2(0,_9M/* Countries.countries255 */,_9L/* Countries.countries254 */),
_9O/* countries248 */ = new T2(1,_9N/* Countries.countries253 */,_9K/* Countries.countries249 */),
_9P/* countries257 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yemen"));
}),
_9Q/* countries258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YE"));
}),
_9R/* countries256 */ = new T2(0,_9Q/* Countries.countries258 */,_9P/* Countries.countries257 */),
_9S/* countries247 */ = new T2(1,_9R/* Countries.countries256 */,_9O/* Countries.countries248 */),
_9T/* countries260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Western Sahara"));
}),
_9U/* countries261 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EH"));
}),
_9V/* countries259 */ = new T2(0,_9U/* Countries.countries261 */,_9T/* Countries.countries260 */),
_9W/* countries246 */ = new T2(1,_9V/* Countries.countries259 */,_9S/* Countries.countries247 */),
_9X/* countries263 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Wallis and Futuna"));
}),
_9Y/* countries264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WF"));
}),
_9Z/* countries262 */ = new T2(0,_9Y/* Countries.countries264 */,_9X/* Countries.countries263 */),
_a0/* countries245 */ = new T2(1,_9Z/* Countries.countries262 */,_9W/* Countries.countries246 */),
_a1/* countries266 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, U.S."));
}),
_a2/* countries267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VI"));
}),
_a3/* countries265 */ = new T2(0,_a2/* Countries.countries267 */,_a1/* Countries.countries266 */),
_a4/* countries244 */ = new T2(1,_a3/* Countries.countries265 */,_a0/* Countries.countries245 */),
_a5/* countries269 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, British"));
}),
_a6/* countries270 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VG"));
}),
_a7/* countries268 */ = new T2(0,_a6/* Countries.countries270 */,_a5/* Countries.countries269 */),
_a8/* countries243 */ = new T2(1,_a7/* Countries.countries268 */,_a4/* Countries.countries244 */),
_a9/* countries272 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Viet Nam"));
}),
_aa/* countries273 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VN"));
}),
_ab/* countries271 */ = new T2(0,_aa/* Countries.countries273 */,_a9/* Countries.countries272 */),
_ac/* countries242 */ = new T2(1,_ab/* Countries.countries271 */,_a8/* Countries.countries243 */),
_ad/* countries275 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Venezuela, Bolivarian Republic of"));
}),
_ae/* countries276 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VE"));
}),
_af/* countries274 */ = new T2(0,_ae/* Countries.countries276 */,_ad/* Countries.countries275 */),
_ag/* countries241 */ = new T2(1,_af/* Countries.countries274 */,_ac/* Countries.countries242 */),
_ah/* countries278 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Vanuatu"));
}),
_ai/* countries279 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VU"));
}),
_aj/* countries277 */ = new T2(0,_ai/* Countries.countries279 */,_ah/* Countries.countries278 */),
_ak/* countries240 */ = new T2(1,_aj/* Countries.countries277 */,_ag/* Countries.countries241 */),
_al/* countries281 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uzbekistan"));
}),
_am/* countries282 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UZ"));
}),
_an/* countries280 */ = new T2(0,_am/* Countries.countries282 */,_al/* Countries.countries281 */),
_ao/* countries239 */ = new T2(1,_an/* Countries.countries280 */,_ak/* Countries.countries240 */),
_ap/* countries284 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uruguay"));
}),
_aq/* countries285 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UY"));
}),
_ar/* countries283 */ = new T2(0,_aq/* Countries.countries285 */,_ap/* Countries.countries284 */),
_as/* countries238 */ = new T2(1,_ar/* Countries.countries283 */,_ao/* Countries.countries239 */),
_at/* countries287 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States Minor Outlying Islands"));
}),
_au/* countries288 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UM"));
}),
_av/* countries286 */ = new T2(0,_au/* Countries.countries288 */,_at/* Countries.countries287 */),
_aw/* countries237 */ = new T2(1,_av/* Countries.countries286 */,_as/* Countries.countries238 */),
_ax/* countries290 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States"));
}),
_ay/* countries291 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_az/* countries289 */ = new T2(0,_ay/* Countries.countries291 */,_ax/* Countries.countries290 */),
_aA/* countries236 */ = new T2(1,_az/* Countries.countries289 */,_aw/* Countries.countries237 */),
_aB/* countries293 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Kingdom"));
}),
_aC/* countries294 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_aD/* countries292 */ = new T2(0,_aC/* Countries.countries294 */,_aB/* Countries.countries293 */),
_aE/* countries235 */ = new T2(1,_aD/* Countries.countries292 */,_aA/* Countries.countries236 */),
_aF/* countries296 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Arab Emirates"));
}),
_aG/* countries297 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AE"));
}),
_aH/* countries295 */ = new T2(0,_aG/* Countries.countries297 */,_aF/* Countries.countries296 */),
_aI/* countries234 */ = new T2(1,_aH/* Countries.countries295 */,_aE/* Countries.countries235 */),
_aJ/* countries299 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ukraine"));
}),
_aK/* countries300 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UA"));
}),
_aL/* countries298 */ = new T2(0,_aK/* Countries.countries300 */,_aJ/* Countries.countries299 */),
_aM/* countries233 */ = new T2(1,_aL/* Countries.countries298 */,_aI/* Countries.countries234 */),
_aN/* countries302 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uganda"));
}),
_aO/* countries303 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UG"));
}),
_aP/* countries301 */ = new T2(0,_aO/* Countries.countries303 */,_aN/* Countries.countries302 */),
_aQ/* countries232 */ = new T2(1,_aP/* Countries.countries301 */,_aM/* Countries.countries233 */),
_aR/* countries305 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tuvalu"));
}),
_aS/* countries306 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TV"));
}),
_aT/* countries304 */ = new T2(0,_aS/* Countries.countries306 */,_aR/* Countries.countries305 */),
_aU/* countries231 */ = new T2(1,_aT/* Countries.countries304 */,_aQ/* Countries.countries232 */),
_aV/* countries308 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turks and Caicos Islands"));
}),
_aW/* countries309 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TC"));
}),
_aX/* countries307 */ = new T2(0,_aW/* Countries.countries309 */,_aV/* Countries.countries308 */),
_aY/* countries230 */ = new T2(1,_aX/* Countries.countries307 */,_aU/* Countries.countries231 */),
_aZ/* countries311 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkmenistan"));
}),
_b0/* countries312 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TM"));
}),
_b1/* countries310 */ = new T2(0,_b0/* Countries.countries312 */,_aZ/* Countries.countries311 */),
_b2/* countries229 */ = new T2(1,_b1/* Countries.countries310 */,_aY/* Countries.countries230 */),
_b3/* countries314 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkey"));
}),
_b4/* countries315 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TR"));
}),
_b5/* countries313 */ = new T2(0,_b4/* Countries.countries315 */,_b3/* Countries.countries314 */),
_b6/* countries228 */ = new T2(1,_b5/* Countries.countries313 */,_b2/* Countries.countries229 */),
_b7/* countries317 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tunisia"));
}),
_b8/* countries318 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TN"));
}),
_b9/* countries316 */ = new T2(0,_b8/* Countries.countries318 */,_b7/* Countries.countries317 */),
_ba/* countries227 */ = new T2(1,_b9/* Countries.countries316 */,_b6/* Countries.countries228 */),
_bb/* countries320 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trinidad and Tobago"));
}),
_bc/* countries321 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TT"));
}),
_bd/* countries319 */ = new T2(0,_bc/* Countries.countries321 */,_bb/* Countries.countries320 */),
_be/* countries226 */ = new T2(1,_bd/* Countries.countries319 */,_ba/* Countries.countries227 */),
_bf/* countries323 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tonga"));
}),
_bg/* countries324 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TO"));
}),
_bh/* countries322 */ = new T2(0,_bg/* Countries.countries324 */,_bf/* Countries.countries323 */),
_bi/* countries225 */ = new T2(1,_bh/* Countries.countries322 */,_be/* Countries.countries226 */),
_bj/* countries326 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tokelau"));
}),
_bk/* countries327 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TK"));
}),
_bl/* countries325 */ = new T2(0,_bk/* Countries.countries327 */,_bj/* Countries.countries326 */),
_bm/* countries224 */ = new T2(1,_bl/* Countries.countries325 */,_bi/* Countries.countries225 */),
_bn/* countries329 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Togo"));
}),
_bo/* countries330 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TG"));
}),
_bp/* countries328 */ = new T2(0,_bo/* Countries.countries330 */,_bn/* Countries.countries329 */),
_bq/* countries223 */ = new T2(1,_bp/* Countries.countries328 */,_bm/* Countries.countries224 */),
_br/* countries332 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Timor-Leste"));
}),
_bs/* countries333 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TL"));
}),
_bt/* countries331 */ = new T2(0,_bs/* Countries.countries333 */,_br/* Countries.countries332 */),
_bu/* countries222 */ = new T2(1,_bt/* Countries.countries331 */,_bq/* Countries.countries223 */),
_bv/* countries335 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Thailand"));
}),
_bw/* countries336 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TH"));
}),
_bx/* countries334 */ = new T2(0,_bw/* Countries.countries336 */,_bv/* Countries.countries335 */),
_by/* countries221 */ = new T2(1,_bx/* Countries.countries334 */,_bu/* Countries.countries222 */),
_bz/* countries338 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tanzania, United Republic of"));
}),
_bA/* countries339 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TZ"));
}),
_bB/* countries337 */ = new T2(0,_bA/* Countries.countries339 */,_bz/* Countries.countries338 */),
_bC/* countries220 */ = new T2(1,_bB/* Countries.countries337 */,_by/* Countries.countries221 */),
_bD/* countries341 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tajikistan"));
}),
_bE/* countries342 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TJ"));
}),
_bF/* countries340 */ = new T2(0,_bE/* Countries.countries342 */,_bD/* Countries.countries341 */),
_bG/* countries219 */ = new T2(1,_bF/* Countries.countries340 */,_bC/* Countries.countries220 */),
_bH/* countries344 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Taiwan, Province of China"));
}),
_bI/* countries345 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TW"));
}),
_bJ/* countries343 */ = new T2(0,_bI/* Countries.countries345 */,_bH/* Countries.countries344 */),
_bK/* countries218 */ = new T2(1,_bJ/* Countries.countries343 */,_bG/* Countries.countries219 */),
_bL/* countries347 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Syrian Arab Republic"));
}),
_bM/* countries348 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SY"));
}),
_bN/* countries346 */ = new T2(0,_bM/* Countries.countries348 */,_bL/* Countries.countries347 */),
_bO/* countries217 */ = new T2(1,_bN/* Countries.countries346 */,_bK/* Countries.countries218 */),
_bP/* countries350 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Switzerland"));
}),
_bQ/* countries351 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CH"));
}),
_bR/* countries349 */ = new T2(0,_bQ/* Countries.countries351 */,_bP/* Countries.countries350 */),
_bS/* countries216 */ = new T2(1,_bR/* Countries.countries349 */,_bO/* Countries.countries217 */),
_bT/* countries353 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sweden"));
}),
_bU/* countries354 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SE"));
}),
_bV/* countries352 */ = new T2(0,_bU/* Countries.countries354 */,_bT/* Countries.countries353 */),
_bW/* countries215 */ = new T2(1,_bV/* Countries.countries352 */,_bS/* Countries.countries216 */),
_bX/* countries356 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Swaziland"));
}),
_bY/* countries357 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SZ"));
}),
_bZ/* countries355 */ = new T2(0,_bY/* Countries.countries357 */,_bX/* Countries.countries356 */),
_c0/* countries214 */ = new T2(1,_bZ/* Countries.countries355 */,_bW/* Countries.countries215 */),
_c1/* countries359 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Svalbard and Jan Mayen"));
}),
_c2/* countries360 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SJ"));
}),
_c3/* countries358 */ = new T2(0,_c2/* Countries.countries360 */,_c1/* Countries.countries359 */),
_c4/* countries213 */ = new T2(1,_c3/* Countries.countries358 */,_c0/* Countries.countries214 */),
_c5/* countries362 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Suriname"));
}),
_c6/* countries363 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SR"));
}),
_c7/* countries361 */ = new T2(0,_c6/* Countries.countries363 */,_c5/* Countries.countries362 */),
_c8/* countries212 */ = new T2(1,_c7/* Countries.countries361 */,_c4/* Countries.countries213 */),
_c9/* countries365 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sudan"));
}),
_ca/* countries366 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SD"));
}),
_cb/* countries364 */ = new T2(0,_ca/* Countries.countries366 */,_c9/* Countries.countries365 */),
_cc/* countries211 */ = new T2(1,_cb/* Countries.countries364 */,_c8/* Countries.countries212 */),
_cd/* countries368 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sri Lanka"));
}),
_ce/* countries369 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LK"));
}),
_cf/* countries367 */ = new T2(0,_ce/* Countries.countries369 */,_cd/* Countries.countries368 */),
_cg/* countries210 */ = new T2(1,_cf/* Countries.countries367 */,_cc/* Countries.countries211 */),
_ch/* countries371 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Spain"));
}),
_ci/* countries372 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ES"));
}),
_cj/* countries370 */ = new T2(0,_ci/* Countries.countries372 */,_ch/* Countries.countries371 */),
_ck/* countries209 */ = new T2(1,_cj/* Countries.countries370 */,_cg/* Countries.countries210 */),
_cl/* countries374 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Sudan"));
}),
_cm/* countries375 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SS"));
}),
_cn/* countries373 */ = new T2(0,_cm/* Countries.countries375 */,_cl/* Countries.countries374 */),
_co/* countries208 */ = new T2(1,_cn/* Countries.countries373 */,_ck/* Countries.countries209 */),
_cp/* countries377 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Georgia and the South Sandwich Islands"));
}),
_cq/* countries378 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_cr/* countries376 */ = new T2(0,_cq/* Countries.countries378 */,_cp/* Countries.countries377 */),
_cs/* countries207 */ = new T2(1,_cr/* Countries.countries376 */,_co/* Countries.countries208 */),
_ct/* countries380 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Africa"));
}),
_cu/* countries381 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZA"));
}),
_cv/* countries379 */ = new T2(0,_cu/* Countries.countries381 */,_ct/* Countries.countries380 */),
_cw/* countries206 */ = new T2(1,_cv/* Countries.countries379 */,_cs/* Countries.countries207 */),
_cx/* countries383 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Somalia"));
}),
_cy/* countries384 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_cz/* countries382 */ = new T2(0,_cy/* Countries.countries384 */,_cx/* Countries.countries383 */),
_cA/* countries205 */ = new T2(1,_cz/* Countries.countries382 */,_cw/* Countries.countries206 */),
_cB/* countries386 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Solomon Islands"));
}),
_cC/* countries387 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SB"));
}),
_cD/* countries385 */ = new T2(0,_cC/* Countries.countries387 */,_cB/* Countries.countries386 */),
_cE/* countries204 */ = new T2(1,_cD/* Countries.countries385 */,_cA/* Countries.countries205 */),
_cF/* countries389 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovenia"));
}),
_cG/* countries390 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_cH/* countries388 */ = new T2(0,_cG/* Countries.countries390 */,_cF/* Countries.countries389 */),
_cI/* countries203 */ = new T2(1,_cH/* Countries.countries388 */,_cE/* Countries.countries204 */),
_cJ/* countries392 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovakia"));
}),
_cK/* countries393 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SK"));
}),
_cL/* countries391 */ = new T2(0,_cK/* Countries.countries393 */,_cJ/* Countries.countries392 */),
_cM/* countries202 */ = new T2(1,_cL/* Countries.countries391 */,_cI/* Countries.countries203 */),
_cN/* countries395 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sint Maarten (Dutch part)"));
}),
_cO/* countries396 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SX"));
}),
_cP/* countries394 */ = new T2(0,_cO/* Countries.countries396 */,_cN/* Countries.countries395 */),
_cQ/* countries201 */ = new T2(1,_cP/* Countries.countries394 */,_cM/* Countries.countries202 */),
_cR/* countries398 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Singapore"));
}),
_cS/* countries399 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SG"));
}),
_cT/* countries397 */ = new T2(0,_cS/* Countries.countries399 */,_cR/* Countries.countries398 */),
_cU/* countries200 */ = new T2(1,_cT/* Countries.countries397 */,_cQ/* Countries.countries201 */),
_cV/* countries401 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sierra Leone"));
}),
_cW/* countries402 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SL"));
}),
_cX/* countries400 */ = new T2(0,_cW/* Countries.countries402 */,_cV/* Countries.countries401 */),
_cY/* countries199 */ = new T2(1,_cX/* Countries.countries400 */,_cU/* Countries.countries200 */),
_cZ/* countries404 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Seychelles"));
}),
_d0/* countries405 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SC"));
}),
_d1/* countries403 */ = new T2(0,_d0/* Countries.countries405 */,_cZ/* Countries.countries404 */),
_d2/* countries198 */ = new T2(1,_d1/* Countries.countries403 */,_cY/* Countries.countries199 */),
_d3/* countries407 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Serbia"));
}),
_d4/* countries408 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_d5/* countries406 */ = new T2(0,_d4/* Countries.countries408 */,_d3/* Countries.countries407 */),
_d6/* countries197 */ = new T2(1,_d5/* Countries.countries406 */,_d2/* Countries.countries198 */),
_d7/* countries410 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Senegal"));
}),
_d8/* countries411 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SN"));
}),
_d9/* countries409 */ = new T2(0,_d8/* Countries.countries411 */,_d7/* Countries.countries410 */),
_da/* countries196 */ = new T2(1,_d9/* Countries.countries409 */,_d6/* Countries.countries197 */),
_db/* countries413 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saudi Arabia"));
}),
_dc/* countries414 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SA"));
}),
_dd/* countries412 */ = new T2(0,_dc/* Countries.countries414 */,_db/* Countries.countries413 */),
_de/* countries195 */ = new T2(1,_dd/* Countries.countries412 */,_da/* Countries.countries196 */),
_df/* countries416 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sao Tome and Principe"));
}),
_dg/* countries417 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ST"));
}),
_dh/* countries415 */ = new T2(0,_dg/* Countries.countries417 */,_df/* Countries.countries416 */),
_di/* countries194 */ = new T2(1,_dh/* Countries.countries415 */,_de/* Countries.countries195 */),
_dj/* countries419 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("San Marino"));
}),
_dk/* countries420 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SM"));
}),
_dl/* countries418 */ = new T2(0,_dk/* Countries.countries420 */,_dj/* Countries.countries419 */),
_dm/* countries193 */ = new T2(1,_dl/* Countries.countries418 */,_di/* Countries.countries194 */),
_dn/* countries422 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Samoa"));
}),
_do/* countries423 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WS"));
}),
_dp/* countries421 */ = new T2(0,_do/* Countries.countries423 */,_dn/* Countries.countries422 */),
_dq/* countries192 */ = new T2(1,_dp/* Countries.countries421 */,_dm/* Countries.countries193 */),
_dr/* countries425 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Vincent and the Grenadines"));
}),
_ds/* countries426 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VC"));
}),
_dt/* countries424 */ = new T2(0,_ds/* Countries.countries426 */,_dr/* Countries.countries425 */),
_du/* countries191 */ = new T2(1,_dt/* Countries.countries424 */,_dq/* Countries.countries192 */),
_dv/* countries428 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Pierre and Miquelon"));
}),
_dw/* countries429 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PM"));
}),
_dx/* countries427 */ = new T2(0,_dw/* Countries.countries429 */,_dv/* Countries.countries428 */),
_dy/* countries190 */ = new T2(1,_dx/* Countries.countries427 */,_du/* Countries.countries191 */),
_dz/* countries431 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Martin (French part)"));
}),
_dA/* countries432 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MF"));
}),
_dB/* countries430 */ = new T2(0,_dA/* Countries.countries432 */,_dz/* Countries.countries431 */),
_dC/* countries189 */ = new T2(1,_dB/* Countries.countries430 */,_dy/* Countries.countries190 */),
_dD/* countries434 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Lucia"));
}),
_dE/* countries435 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LC"));
}),
_dF/* countries433 */ = new T2(0,_dE/* Countries.countries435 */,_dD/* Countries.countries434 */),
_dG/* countries188 */ = new T2(1,_dF/* Countries.countries433 */,_dC/* Countries.countries189 */),
_dH/* countries437 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Kitts and Nevis"));
}),
_dI/* countries438 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KN"));
}),
_dJ/* countries436 */ = new T2(0,_dI/* Countries.countries438 */,_dH/* Countries.countries437 */),
_dK/* countries187 */ = new T2(1,_dJ/* Countries.countries436 */,_dG/* Countries.countries188 */),
_dL/* countries440 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Helena, Ascension and Tristan da Cunha"));
}),
_dM/* countries441 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SH"));
}),
_dN/* countries439 */ = new T2(0,_dM/* Countries.countries441 */,_dL/* Countries.countries440 */),
_dO/* countries186 */ = new T2(1,_dN/* Countries.countries439 */,_dK/* Countries.countries187 */),
_dP/* countries443 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Barth\u00e9lemy"));
}),
_dQ/* countries444 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BL"));
}),
_dR/* countries442 */ = new T2(0,_dQ/* Countries.countries444 */,_dP/* Countries.countries443 */),
_dS/* countries185 */ = new T2(1,_dR/* Countries.countries442 */,_dO/* Countries.countries186 */),
_dT/* countries446 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rwanda"));
}),
_dU/* countries447 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RW"));
}),
_dV/* countries445 */ = new T2(0,_dU/* Countries.countries447 */,_dT/* Countries.countries446 */),
_dW/* countries184 */ = new T2(1,_dV/* Countries.countries445 */,_dS/* Countries.countries185 */),
_dX/* countries449 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Russian Federation"));
}),
_dY/* countries450 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RU"));
}),
_dZ/* countries448 */ = new T2(0,_dY/* Countries.countries450 */,_dX/* Countries.countries449 */),
_e0/* countries183 */ = new T2(1,_dZ/* Countries.countries448 */,_dW/* Countries.countries184 */),
_e1/* countries452 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Romania"));
}),
_e2/* countries453 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RO"));
}),
_e3/* countries451 */ = new T2(0,_e2/* Countries.countries453 */,_e1/* Countries.countries452 */),
_e4/* countries182 */ = new T2(1,_e3/* Countries.countries451 */,_e0/* Countries.countries183 */),
_e5/* countries455 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("R\u00e9union"));
}),
_e6/* countries456 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RE"));
}),
_e7/* countries454 */ = new T2(0,_e6/* Countries.countries456 */,_e5/* Countries.countries455 */),
_e8/* countries181 */ = new T2(1,_e7/* Countries.countries454 */,_e4/* Countries.countries182 */),
_e9/* countries458 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Qatar"));
}),
_ea/* countries459 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("QA"));
}),
_eb/* countries457 */ = new T2(0,_ea/* Countries.countries459 */,_e9/* Countries.countries458 */),
_ec/* countries180 */ = new T2(1,_eb/* Countries.countries457 */,_e8/* Countries.countries181 */),
_ed/* countries461 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Puerto Rico"));
}),
_ee/* countries462 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PR"));
}),
_ef/* countries460 */ = new T2(0,_ee/* Countries.countries462 */,_ed/* Countries.countries461 */),
_eg/* countries179 */ = new T2(1,_ef/* Countries.countries460 */,_ec/* Countries.countries180 */),
_eh/* countries464 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Portugal"));
}),
_ei/* countries465 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PT"));
}),
_ej/* countries463 */ = new T2(0,_ei/* Countries.countries465 */,_eh/* Countries.countries464 */),
_ek/* countries178 */ = new T2(1,_ej/* Countries.countries463 */,_eg/* Countries.countries179 */),
_el/* countries467 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Poland"));
}),
_em/* countries468 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PL"));
}),
_en/* countries466 */ = new T2(0,_em/* Countries.countries468 */,_el/* Countries.countries467 */),
_eo/* countries177 */ = new T2(1,_en/* Countries.countries466 */,_ek/* Countries.countries178 */),
_ep/* countries470 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pitcairn"));
}),
_eq/* countries471 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PN"));
}),
_er/* countries469 */ = new T2(0,_eq/* Countries.countries471 */,_ep/* Countries.countries470 */),
_es/* countries176 */ = new T2(1,_er/* Countries.countries469 */,_eo/* Countries.countries177 */),
_et/* countries473 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Philippines"));
}),
_eu/* countries474 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PH"));
}),
_ev/* countries472 */ = new T2(0,_eu/* Countries.countries474 */,_et/* Countries.countries473 */),
_ew/* countries175 */ = new T2(1,_ev/* Countries.countries472 */,_es/* Countries.countries176 */),
_ex/* countries476 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Peru"));
}),
_ey/* countries477 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PE"));
}),
_ez/* countries475 */ = new T2(0,_ey/* Countries.countries477 */,_ex/* Countries.countries476 */),
_eA/* countries174 */ = new T2(1,_ez/* Countries.countries475 */,_ew/* Countries.countries175 */),
_eB/* countries479 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Paraguay"));
}),
_eC/* countries480 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PY"));
}),
_eD/* countries478 */ = new T2(0,_eC/* Countries.countries480 */,_eB/* Countries.countries479 */),
_eE/* countries173 */ = new T2(1,_eD/* Countries.countries478 */,_eA/* Countries.countries174 */),
_eF/* countries482 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Papua New Guinea"));
}),
_eG/* countries483 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PG"));
}),
_eH/* countries481 */ = new T2(0,_eG/* Countries.countries483 */,_eF/* Countries.countries482 */),
_eI/* countries172 */ = new T2(1,_eH/* Countries.countries481 */,_eE/* Countries.countries173 */),
_eJ/* countries485 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Panama"));
}),
_eK/* countries486 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PA"));
}),
_eL/* countries484 */ = new T2(0,_eK/* Countries.countries486 */,_eJ/* Countries.countries485 */),
_eM/* countries171 */ = new T2(1,_eL/* Countries.countries484 */,_eI/* Countries.countries172 */),
_eN/* countries488 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palestinian Territory, Occupied"));
}),
_eO/* countries489 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PS"));
}),
_eP/* countries487 */ = new T2(0,_eO/* Countries.countries489 */,_eN/* Countries.countries488 */),
_eQ/* countries170 */ = new T2(1,_eP/* Countries.countries487 */,_eM/* Countries.countries171 */),
_eR/* countries491 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palau"));
}),
_eS/* countries492 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PW"));
}),
_eT/* countries490 */ = new T2(0,_eS/* Countries.countries492 */,_eR/* Countries.countries491 */),
_eU/* countries169 */ = new T2(1,_eT/* Countries.countries490 */,_eQ/* Countries.countries170 */),
_eV/* countries494 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pakistan"));
}),
_eW/* countries495 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PK"));
}),
_eX/* countries493 */ = new T2(0,_eW/* Countries.countries495 */,_eV/* Countries.countries494 */),
_eY/* countries168 */ = new T2(1,_eX/* Countries.countries493 */,_eU/* Countries.countries169 */),
_eZ/* countries497 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Oman"));
}),
_f0/* countries498 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OM"));
}),
_f1/* countries496 */ = new T2(0,_f0/* Countries.countries498 */,_eZ/* Countries.countries497 */),
_f2/* countries167 */ = new T2(1,_f1/* Countries.countries496 */,_eY/* Countries.countries168 */),
_f3/* countries500 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norway"));
}),
_f4/* countries501 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NO"));
}),
_f5/* countries499 */ = new T2(0,_f4/* Countries.countries501 */,_f3/* Countries.countries500 */),
_f6/* countries166 */ = new T2(1,_f5/* Countries.countries499 */,_f2/* Countries.countries167 */),
_f7/* countries503 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Northern Mariana Islands"));
}),
_f8/* countries504 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MP"));
}),
_f9/* countries502 */ = new T2(0,_f8/* Countries.countries504 */,_f7/* Countries.countries503 */),
_fa/* countries165 */ = new T2(1,_f9/* Countries.countries502 */,_f6/* Countries.countries166 */),
_fb/* countries506 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norfolk Island"));
}),
_fc/* countries507 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NF"));
}),
_fd/* countries505 */ = new T2(0,_fc/* Countries.countries507 */,_fb/* Countries.countries506 */),
_fe/* countries164 */ = new T2(1,_fd/* Countries.countries505 */,_fa/* Countries.countries165 */),
_ff/* countries509 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niue"));
}),
_fg/* countries510 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NU"));
}),
_fh/* countries508 */ = new T2(0,_fg/* Countries.countries510 */,_ff/* Countries.countries509 */),
_fi/* countries163 */ = new T2(1,_fh/* Countries.countries508 */,_fe/* Countries.countries164 */),
_fj/* countries512 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nigeria"));
}),
_fk/* countries513 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NG"));
}),
_fl/* countries511 */ = new T2(0,_fk/* Countries.countries513 */,_fj/* Countries.countries512 */),
_fm/* countries162 */ = new T2(1,_fl/* Countries.countries511 */,_fi/* Countries.countries163 */),
_fn/* countries515 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niger"));
}),
_fo/* countries516 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NE"));
}),
_fp/* countries514 */ = new T2(0,_fo/* Countries.countries516 */,_fn/* Countries.countries515 */),
_fq/* countries161 */ = new T2(1,_fp/* Countries.countries514 */,_fm/* Countries.countries162 */),
_fr/* countries518 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nicaragua"));
}),
_fs/* countries519 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NI"));
}),
_ft/* countries517 */ = new T2(0,_fs/* Countries.countries519 */,_fr/* Countries.countries518 */),
_fu/* countries160 */ = new T2(1,_ft/* Countries.countries517 */,_fq/* Countries.countries161 */),
_fv/* countries521 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Zealand"));
}),
_fw/* countries522 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NZ"));
}),
_fx/* countries520 */ = new T2(0,_fw/* Countries.countries522 */,_fv/* Countries.countries521 */),
_fy/* countries159 */ = new T2(1,_fx/* Countries.countries520 */,_fu/* Countries.countries160 */),
_fz/* countries524 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Caledonia"));
}),
_fA/* countries525 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NC"));
}),
_fB/* countries523 */ = new T2(0,_fA/* Countries.countries525 */,_fz/* Countries.countries524 */),
_fC/* countries158 */ = new T2(1,_fB/* Countries.countries523 */,_fy/* Countries.countries159 */),
_fD/* countries527 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Netherlands"));
}),
_fE/* countries528 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NL"));
}),
_fF/* countries526 */ = new T2(0,_fE/* Countries.countries528 */,_fD/* Countries.countries527 */),
_fG/* countries157 */ = new T2(1,_fF/* Countries.countries526 */,_fC/* Countries.countries158 */),
_fH/* countries530 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nepal"));
}),
_fI/* countries531 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NP"));
}),
_fJ/* countries529 */ = new T2(0,_fI/* Countries.countries531 */,_fH/* Countries.countries530 */),
_fK/* countries156 */ = new T2(1,_fJ/* Countries.countries529 */,_fG/* Countries.countries157 */),
_fL/* countries533 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nauru"));
}),
_fM/* countries534 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NR"));
}),
_fN/* countries532 */ = new T2(0,_fM/* Countries.countries534 */,_fL/* Countries.countries533 */),
_fO/* countries155 */ = new T2(1,_fN/* Countries.countries532 */,_fK/* Countries.countries156 */),
_fP/* countries536 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Namibia"));
}),
_fQ/* countries537 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NA"));
}),
_fR/* countries535 */ = new T2(0,_fQ/* Countries.countries537 */,_fP/* Countries.countries536 */),
_fS/* countries154 */ = new T2(1,_fR/* Countries.countries535 */,_fO/* Countries.countries155 */),
_fT/* countries539 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Myanmar"));
}),
_fU/* countries540 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MM"));
}),
_fV/* countries538 */ = new T2(0,_fU/* Countries.countries540 */,_fT/* Countries.countries539 */),
_fW/* countries153 */ = new T2(1,_fV/* Countries.countries538 */,_fS/* Countries.countries154 */),
_fX/* countries542 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mozambique"));
}),
_fY/* countries543 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MZ"));
}),
_fZ/* countries541 */ = new T2(0,_fY/* Countries.countries543 */,_fX/* Countries.countries542 */),
_g0/* countries152 */ = new T2(1,_fZ/* Countries.countries541 */,_fW/* Countries.countries153 */),
_g1/* countries545 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Morocco"));
}),
_g2/* countries546 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MA"));
}),
_g3/* countries544 */ = new T2(0,_g2/* Countries.countries546 */,_g1/* Countries.countries545 */),
_g4/* countries151 */ = new T2(1,_g3/* Countries.countries544 */,_g0/* Countries.countries152 */),
_g5/* countries548 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montserrat"));
}),
_g6/* countries549 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MS"));
}),
_g7/* countries547 */ = new T2(0,_g6/* Countries.countries549 */,_g5/* Countries.countries548 */),
_g8/* countries150 */ = new T2(1,_g7/* Countries.countries547 */,_g4/* Countries.countries151 */),
_g9/* countries551 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montenegro"));
}),
_ga/* countries552 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ME"));
}),
_gb/* countries550 */ = new T2(0,_ga/* Countries.countries552 */,_g9/* Countries.countries551 */),
_gc/* countries149 */ = new T2(1,_gb/* Countries.countries550 */,_g8/* Countries.countries150 */),
_gd/* countries554 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mongolia"));
}),
_ge/* countries555 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MN"));
}),
_gf/* countries553 */ = new T2(0,_ge/* Countries.countries555 */,_gd/* Countries.countries554 */),
_gg/* countries148 */ = new T2(1,_gf/* Countries.countries553 */,_gc/* Countries.countries149 */),
_gh/* countries557 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Monaco"));
}),
_gi/* countries558 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MC"));
}),
_gj/* countries556 */ = new T2(0,_gi/* Countries.countries558 */,_gh/* Countries.countries557 */),
_gk/* countries147 */ = new T2(1,_gj/* Countries.countries556 */,_gg/* Countries.countries148 */),
_gl/* countries560 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Moldova, Republic of"));
}),
_gm/* countries561 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MD"));
}),
_gn/* countries559 */ = new T2(0,_gm/* Countries.countries561 */,_gl/* Countries.countries560 */),
_go/* countries146 */ = new T2(1,_gn/* Countries.countries559 */,_gk/* Countries.countries147 */),
_gp/* countries563 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Micronesia, Federated States of"));
}),
_gq/* countries564 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FM"));
}),
_gr/* countries562 */ = new T2(0,_gq/* Countries.countries564 */,_gp/* Countries.countries563 */),
_gs/* countries145 */ = new T2(1,_gr/* Countries.countries562 */,_go/* Countries.countries146 */),
_gt/* countries566 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mexico"));
}),
_gu/* countries567 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MX"));
}),
_gv/* countries565 */ = new T2(0,_gu/* Countries.countries567 */,_gt/* Countries.countries566 */),
_gw/* countries144 */ = new T2(1,_gv/* Countries.countries565 */,_gs/* Countries.countries145 */),
_gx/* countries569 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mayotte"));
}),
_gy/* countries570 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YT"));
}),
_gz/* countries568 */ = new T2(0,_gy/* Countries.countries570 */,_gx/* Countries.countries569 */),
_gA/* countries143 */ = new T2(1,_gz/* Countries.countries568 */,_gw/* Countries.countries144 */),
_gB/* countries572 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritius"));
}),
_gC/* countries573 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MU"));
}),
_gD/* countries571 */ = new T2(0,_gC/* Countries.countries573 */,_gB/* Countries.countries572 */),
_gE/* countries142 */ = new T2(1,_gD/* Countries.countries571 */,_gA/* Countries.countries143 */),
_gF/* countries575 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritania"));
}),
_gG/* countries576 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MR"));
}),
_gH/* countries574 */ = new T2(0,_gG/* Countries.countries576 */,_gF/* Countries.countries575 */),
_gI/* countries141 */ = new T2(1,_gH/* Countries.countries574 */,_gE/* Countries.countries142 */),
_gJ/* countries578 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Martinique"));
}),
_gK/* countries579 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MQ"));
}),
_gL/* countries577 */ = new T2(0,_gK/* Countries.countries579 */,_gJ/* Countries.countries578 */),
_gM/* countries140 */ = new T2(1,_gL/* Countries.countries577 */,_gI/* Countries.countries141 */),
_gN/* countries581 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Marshall Islands"));
}),
_gO/* countries582 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MH"));
}),
_gP/* countries580 */ = new T2(0,_gO/* Countries.countries582 */,_gN/* Countries.countries581 */),
_gQ/* countries139 */ = new T2(1,_gP/* Countries.countries580 */,_gM/* Countries.countries140 */),
_gR/* countries584 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malta"));
}),
_gS/* countries585 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MT"));
}),
_gT/* countries583 */ = new T2(0,_gS/* Countries.countries585 */,_gR/* Countries.countries584 */),
_gU/* countries138 */ = new T2(1,_gT/* Countries.countries583 */,_gQ/* Countries.countries139 */),
_gV/* countries587 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mali"));
}),
_gW/* countries588 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ML"));
}),
_gX/* countries586 */ = new T2(0,_gW/* Countries.countries588 */,_gV/* Countries.countries587 */),
_gY/* countries137 */ = new T2(1,_gX/* Countries.countries586 */,_gU/* Countries.countries138 */),
_gZ/* countries590 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maldives"));
}),
_h0/* countries591 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MV"));
}),
_h1/* countries589 */ = new T2(0,_h0/* Countries.countries591 */,_gZ/* Countries.countries590 */),
_h2/* countries136 */ = new T2(1,_h1/* Countries.countries589 */,_gY/* Countries.countries137 */),
_h3/* countries593 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malaysia"));
}),
_h4/* countries594 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MY"));
}),
_h5/* countries592 */ = new T2(0,_h4/* Countries.countries594 */,_h3/* Countries.countries593 */),
_h6/* countries135 */ = new T2(1,_h5/* Countries.countries592 */,_h2/* Countries.countries136 */),
_h7/* countries596 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malawi"));
}),
_h8/* countries597 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MW"));
}),
_h9/* countries595 */ = new T2(0,_h8/* Countries.countries597 */,_h7/* Countries.countries596 */),
_ha/* countries134 */ = new T2(1,_h9/* Countries.countries595 */,_h6/* Countries.countries135 */),
_hb/* countries599 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Madagascar"));
}),
_hc/* countries600 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MG"));
}),
_hd/* countries598 */ = new T2(0,_hc/* Countries.countries600 */,_hb/* Countries.countries599 */),
_he/* countries133 */ = new T2(1,_hd/* Countries.countries598 */,_ha/* Countries.countries134 */),
_hf/* countries602 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macedonia, the former Yugoslav Republic of"));
}),
_hg/* countries603 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MK"));
}),
_hh/* countries601 */ = new T2(0,_hg/* Countries.countries603 */,_hf/* Countries.countries602 */),
_hi/* countries132 */ = new T2(1,_hh/* Countries.countries601 */,_he/* Countries.countries133 */),
_hj/* countries605 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macao"));
}),
_hk/* countries606 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MO"));
}),
_hl/* countries604 */ = new T2(0,_hk/* Countries.countries606 */,_hj/* Countries.countries605 */),
_hm/* countries131 */ = new T2(1,_hl/* Countries.countries604 */,_hi/* Countries.countries132 */),
_hn/* countries608 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Luxembourg"));
}),
_ho/* countries609 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LU"));
}),
_hp/* countries607 */ = new T2(0,_ho/* Countries.countries609 */,_hn/* Countries.countries608 */),
_hq/* countries130 */ = new T2(1,_hp/* Countries.countries607 */,_hm/* Countries.countries131 */),
_hr/* countries611 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lithuania"));
}),
_hs/* countries612 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LT"));
}),
_ht/* countries610 */ = new T2(0,_hs/* Countries.countries612 */,_hr/* Countries.countries611 */),
_hu/* countries129 */ = new T2(1,_ht/* Countries.countries610 */,_hq/* Countries.countries130 */),
_hv/* countries614 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liechtenstein"));
}),
_hw/* countries615 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LI"));
}),
_hx/* countries613 */ = new T2(0,_hw/* Countries.countries615 */,_hv/* Countries.countries614 */),
_hy/* countries128 */ = new T2(1,_hx/* Countries.countries613 */,_hu/* Countries.countries129 */),
_hz/* countries617 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Libya"));
}),
_hA/* countries618 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LY"));
}),
_hB/* countries616 */ = new T2(0,_hA/* Countries.countries618 */,_hz/* Countries.countries617 */),
_hC/* countries127 */ = new T2(1,_hB/* Countries.countries616 */,_hy/* Countries.countries128 */),
_hD/* countries620 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liberia"));
}),
_hE/* countries621 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LR"));
}),
_hF/* countries619 */ = new T2(0,_hE/* Countries.countries621 */,_hD/* Countries.countries620 */),
_hG/* countries126 */ = new T2(1,_hF/* Countries.countries619 */,_hC/* Countries.countries127 */),
_hH/* countries623 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lesotho"));
}),
_hI/* countries624 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LS"));
}),
_hJ/* countries622 */ = new T2(0,_hI/* Countries.countries624 */,_hH/* Countries.countries623 */),
_hK/* countries125 */ = new T2(1,_hJ/* Countries.countries622 */,_hG/* Countries.countries126 */),
_hL/* countries626 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lebanon"));
}),
_hM/* countries627 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LB"));
}),
_hN/* countries625 */ = new T2(0,_hM/* Countries.countries627 */,_hL/* Countries.countries626 */),
_hO/* countries124 */ = new T2(1,_hN/* Countries.countries625 */,_hK/* Countries.countries125 */),
_hP/* countries629 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Latvia"));
}),
_hQ/* countries630 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LV"));
}),
_hR/* countries628 */ = new T2(0,_hQ/* Countries.countries630 */,_hP/* Countries.countries629 */),
_hS/* countries123 */ = new T2(1,_hR/* Countries.countries628 */,_hO/* Countries.countries124 */),
_hT/* countries632 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lao People\'s Democratic Republic"));
}),
_hU/* countries633 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LA"));
}),
_hV/* countries631 */ = new T2(0,_hU/* Countries.countries633 */,_hT/* Countries.countries632 */),
_hW/* countries122 */ = new T2(1,_hV/* Countries.countries631 */,_hS/* Countries.countries123 */),
_hX/* countries635 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kyrgyzstan"));
}),
_hY/* countries636 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KG"));
}),
_hZ/* countries634 */ = new T2(0,_hY/* Countries.countries636 */,_hX/* Countries.countries635 */),
_i0/* countries121 */ = new T2(1,_hZ/* Countries.countries634 */,_hW/* Countries.countries122 */),
_i1/* countries638 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kuwait"));
}),
_i2/* countries639 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KW"));
}),
_i3/* countries637 */ = new T2(0,_i2/* Countries.countries639 */,_i1/* Countries.countries638 */),
_i4/* countries120 */ = new T2(1,_i3/* Countries.countries637 */,_i0/* Countries.countries121 */),
_i5/* countries641 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Republic of"));
}),
_i6/* countries642 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KR"));
}),
_i7/* countries640 */ = new T2(0,_i6/* Countries.countries642 */,_i5/* Countries.countries641 */),
_i8/* countries119 */ = new T2(1,_i7/* Countries.countries640 */,_i4/* Countries.countries120 */),
_i9/* countries644 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Democratic People\'s Republic of"));
}),
_ia/* countries645 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KP"));
}),
_ib/* countries643 */ = new T2(0,_ia/* Countries.countries645 */,_i9/* Countries.countries644 */),
_ic/* countries118 */ = new T2(1,_ib/* Countries.countries643 */,_i8/* Countries.countries119 */),
_id/* countries647 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kiribati"));
}),
_ie/* countries648 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KI"));
}),
_if/* countries646 */ = new T2(0,_ie/* Countries.countries648 */,_id/* Countries.countries647 */),
_ig/* countries117 */ = new T2(1,_if/* Countries.countries646 */,_ic/* Countries.countries118 */),
_ih/* countries650 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kenya"));
}),
_ii/* countries651 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KE"));
}),
_ij/* countries649 */ = new T2(0,_ii/* Countries.countries651 */,_ih/* Countries.countries650 */),
_ik/* countries116 */ = new T2(1,_ij/* Countries.countries649 */,_ig/* Countries.countries117 */),
_il/* countries653 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kazakhstan"));
}),
_im/* countries654 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KZ"));
}),
_in/* countries652 */ = new T2(0,_im/* Countries.countries654 */,_il/* Countries.countries653 */),
_io/* countries115 */ = new T2(1,_in/* Countries.countries652 */,_ik/* Countries.countries116 */),
_ip/* countries656 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jordan"));
}),
_iq/* countries657 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JO"));
}),
_ir/* countries655 */ = new T2(0,_iq/* Countries.countries657 */,_ip/* Countries.countries656 */),
_is/* countries114 */ = new T2(1,_ir/* Countries.countries655 */,_io/* Countries.countries115 */),
_it/* countries659 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jersey"));
}),
_iu/* countries660 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JE"));
}),
_iv/* countries658 */ = new T2(0,_iu/* Countries.countries660 */,_it/* Countries.countries659 */),
_iw/* countries113 */ = new T2(1,_iv/* Countries.countries658 */,_is/* Countries.countries114 */),
_ix/* countries662 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Japan"));
}),
_iy/* countries663 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JP"));
}),
_iz/* countries661 */ = new T2(0,_iy/* Countries.countries663 */,_ix/* Countries.countries662 */),
_iA/* countries112 */ = new T2(1,_iz/* Countries.countries661 */,_iw/* Countries.countries113 */),
_iB/* countries665 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jamaica"));
}),
_iC/* countries666 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JM"));
}),
_iD/* countries664 */ = new T2(0,_iC/* Countries.countries666 */,_iB/* Countries.countries665 */),
_iE/* countries111 */ = new T2(1,_iD/* Countries.countries664 */,_iA/* Countries.countries112 */),
_iF/* countries668 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Italy"));
}),
_iG/* countries669 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IT"));
}),
_iH/* countries667 */ = new T2(0,_iG/* Countries.countries669 */,_iF/* Countries.countries668 */),
_iI/* countries110 */ = new T2(1,_iH/* Countries.countries667 */,_iE/* Countries.countries111 */),
_iJ/* countries671 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Israel"));
}),
_iK/* countries672 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IL"));
}),
_iL/* countries670 */ = new T2(0,_iK/* Countries.countries672 */,_iJ/* Countries.countries671 */),
_iM/* countries109 */ = new T2(1,_iL/* Countries.countries670 */,_iI/* Countries.countries110 */),
_iN/* countries674 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Isle of Man"));
}),
_iO/* countries675 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IM"));
}),
_iP/* countries673 */ = new T2(0,_iO/* Countries.countries675 */,_iN/* Countries.countries674 */),
_iQ/* countries108 */ = new T2(1,_iP/* Countries.countries673 */,_iM/* Countries.countries109 */),
_iR/* countries677 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ireland"));
}),
_iS/* countries678 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IE"));
}),
_iT/* countries676 */ = new T2(0,_iS/* Countries.countries678 */,_iR/* Countries.countries677 */),
_iU/* countries107 */ = new T2(1,_iT/* Countries.countries676 */,_iQ/* Countries.countries108 */),
_iV/* countries680 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iraq"));
}),
_iW/* countries681 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IQ"));
}),
_iX/* countries679 */ = new T2(0,_iW/* Countries.countries681 */,_iV/* Countries.countries680 */),
_iY/* countries106 */ = new T2(1,_iX/* Countries.countries679 */,_iU/* Countries.countries107 */),
_iZ/* countries683 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iran, Islamic Republic of"));
}),
_j0/* countries684 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IR"));
}),
_j1/* countries682 */ = new T2(0,_j0/* Countries.countries684 */,_iZ/* Countries.countries683 */),
_j2/* countries105 */ = new T2(1,_j1/* Countries.countries682 */,_iY/* Countries.countries106 */),
_j3/* countries686 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Indonesia"));
}),
_j4/* countries687 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ID"));
}),
_j5/* countries685 */ = new T2(0,_j4/* Countries.countries687 */,_j3/* Countries.countries686 */),
_j6/* countries104 */ = new T2(1,_j5/* Countries.countries685 */,_j2/* Countries.countries105 */),
_j7/* countries689 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("India"));
}),
_j8/* countries690 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IN"));
}),
_j9/* countries688 */ = new T2(0,_j8/* Countries.countries690 */,_j7/* Countries.countries689 */),
_ja/* countries103 */ = new T2(1,_j9/* Countries.countries688 */,_j6/* Countries.countries104 */),
_jb/* countries692 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iceland"));
}),
_jc/* countries693 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IS"));
}),
_jd/* countries691 */ = new T2(0,_jc/* Countries.countries693 */,_jb/* Countries.countries692 */),
_je/* countries102 */ = new T2(1,_jd/* Countries.countries691 */,_ja/* Countries.countries103 */),
_jf/* countries695 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hungary"));
}),
_jg/* countries696 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HU"));
}),
_jh/* countries694 */ = new T2(0,_jg/* Countries.countries696 */,_jf/* Countries.countries695 */),
_ji/* countries101 */ = new T2(1,_jh/* Countries.countries694 */,_je/* Countries.countries102 */),
_jj/* countries698 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hong Kong"));
}),
_jk/* countries699 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HK"));
}),
_jl/* countries697 */ = new T2(0,_jk/* Countries.countries699 */,_jj/* Countries.countries698 */),
_jm/* countries100 */ = new T2(1,_jl/* Countries.countries697 */,_ji/* Countries.countries101 */),
_jn/* countries701 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Honduras"));
}),
_jo/* countries702 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HN"));
}),
_jp/* countries700 */ = new T2(0,_jo/* Countries.countries702 */,_jn/* Countries.countries701 */),
_jq/* countries99 */ = new T2(1,_jp/* Countries.countries700 */,_jm/* Countries.countries100 */),
_jr/* countries98 */ = new T2(1,_9G/* Countries.countries703 */,_jq/* Countries.countries99 */),
_js/* countries97 */ = new T2(1,_9D/* Countries.countries706 */,_jr/* Countries.countries98 */),
_jt/* countries96 */ = new T2(1,_9A/* Countries.countries709 */,_js/* Countries.countries97 */),
_ju/* countries95 */ = new T2(1,_9x/* Countries.countries712 */,_jt/* Countries.countries96 */),
_jv/* countries94 */ = new T2(1,_9u/* Countries.countries715 */,_ju/* Countries.countries95 */),
_jw/* countries93 */ = new T2(1,_9r/* Countries.countries718 */,_jv/* Countries.countries94 */),
_jx/* countries92 */ = new T2(1,_9o/* Countries.countries721 */,_jw/* Countries.countries93 */),
_jy/* countries91 */ = new T2(1,_9l/* Countries.countries724 */,_jx/* Countries.countries92 */),
_jz/* countries90 */ = new T2(1,_9i/* Countries.countries727 */,_jy/* Countries.countries91 */),
_jA/* countries89 */ = new T2(1,_9f/* Countries.countries730 */,_jz/* Countries.countries90 */),
_jB/* countries88 */ = new T2(1,_9c/* Countries.countries733 */,_jA/* Countries.countries89 */),
_jC/* countries87 */ = new T2(1,_99/* Countries.countries736 */,_jB/* Countries.countries88 */),
_jD/* countries86 */ = new T2(1,_96/* Countries.countries739 */,_jC/* Countries.countries87 */),
_jE/* countries85 */ = new T2(1,_93/* Countries.countries742 */,_jD/* Countries.countries86 */),
_jF/* countries84 */ = new T2(1,_90/* Countries.countries745 */,_jE/* Countries.countries85 */),
_jG/* countries83 */ = new T2(1,_8X/* Countries.countries748 */,_jF/* Countries.countries84 */),
_jH/* countries82 */ = new T2(1,_8U/* Countries.countries751 */,_jG/* Countries.countries83 */),
_jI/* countries81 */ = new T2(1,_8R/* Countries.countries754 */,_jH/* Countries.countries82 */),
_jJ/* countries80 */ = new T2(1,_8O/* Countries.countries757 */,_jI/* Countries.countries81 */),
_jK/* countries79 */ = new T2(1,_8L/* Countries.countries760 */,_jJ/* Countries.countries80 */),
_jL/* countries78 */ = new T2(1,_8I/* Countries.countries763 */,_jK/* Countries.countries79 */),
_jM/* countries77 */ = new T2(1,_8F/* Countries.countries766 */,_jL/* Countries.countries78 */),
_jN/* countries76 */ = new T2(1,_8C/* Countries.countries769 */,_jM/* Countries.countries77 */),
_jO/* countries773 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finland"));
}),
_jP/* countries774 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FI"));
}),
_jQ/* countries772 */ = new T2(0,_jP/* Countries.countries774 */,_jO/* Countries.countries773 */),
_jR/* countries75 */ = new T2(1,_jQ/* Countries.countries772 */,_jN/* Countries.countries76 */),
_jS/* countries776 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Fiji"));
}),
_jT/* countries777 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FJ"));
}),
_jU/* countries775 */ = new T2(0,_jT/* Countries.countries777 */,_jS/* Countries.countries776 */),
_jV/* countries74 */ = new T2(1,_jU/* Countries.countries775 */,_jR/* Countries.countries75 */),
_jW/* countries779 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Faroe Islands"));
}),
_jX/* countries780 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FO"));
}),
_jY/* countries778 */ = new T2(0,_jX/* Countries.countries780 */,_jW/* Countries.countries779 */),
_jZ/* countries73 */ = new T2(1,_jY/* Countries.countries778 */,_jV/* Countries.countries74 */),
_k0/* countries782 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Falkland Islands (Malvinas)"));
}),
_k1/* countries783 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FK"));
}),
_k2/* countries781 */ = new T2(0,_k1/* Countries.countries783 */,_k0/* Countries.countries782 */),
_k3/* countries72 */ = new T2(1,_k2/* Countries.countries781 */,_jZ/* Countries.countries73 */),
_k4/* countries785 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ethiopia"));
}),
_k5/* countries786 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ET"));
}),
_k6/* countries784 */ = new T2(0,_k5/* Countries.countries786 */,_k4/* Countries.countries785 */),
_k7/* countries71 */ = new T2(1,_k6/* Countries.countries784 */,_k3/* Countries.countries72 */),
_k8/* countries788 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Estonia"));
}),
_k9/* countries789 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EE"));
}),
_ka/* countries787 */ = new T2(0,_k9/* Countries.countries789 */,_k8/* Countries.countries788 */),
_kb/* countries70 */ = new T2(1,_ka/* Countries.countries787 */,_k7/* Countries.countries71 */),
_kc/* countries791 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Eritrea"));
}),
_kd/* countries792 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ER"));
}),
_ke/* countries790 */ = new T2(0,_kd/* Countries.countries792 */,_kc/* Countries.countries791 */),
_kf/* countries69 */ = new T2(1,_ke/* Countries.countries790 */,_kb/* Countries.countries70 */),
_kg/* countries794 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Equatorial Guinea"));
}),
_kh/* countries795 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GQ"));
}),
_ki/* countries793 */ = new T2(0,_kh/* Countries.countries795 */,_kg/* Countries.countries794 */),
_kj/* countries68 */ = new T2(1,_ki/* Countries.countries793 */,_kf/* Countries.countries69 */),
_kk/* countries797 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("El Salvador"));
}),
_kl/* countries798 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SV"));
}),
_km/* countries796 */ = new T2(0,_kl/* Countries.countries798 */,_kk/* Countries.countries797 */),
_kn/* countries67 */ = new T2(1,_km/* Countries.countries796 */,_kj/* Countries.countries68 */),
_ko/* countries800 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Egypt"));
}),
_kp/* countries801 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EG"));
}),
_kq/* countries799 */ = new T2(0,_kp/* Countries.countries801 */,_ko/* Countries.countries800 */),
_kr/* countries66 */ = new T2(1,_kq/* Countries.countries799 */,_kn/* Countries.countries67 */),
_ks/* countries803 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ecuador"));
}),
_kt/* countries804 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EC"));
}),
_ku/* countries802 */ = new T2(0,_kt/* Countries.countries804 */,_ks/* Countries.countries803 */),
_kv/* countries65 */ = new T2(1,_ku/* Countries.countries802 */,_kr/* Countries.countries66 */),
_kw/* countries806 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominican Republic"));
}),
_kx/* countries807 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DO"));
}),
_ky/* countries805 */ = new T2(0,_kx/* Countries.countries807 */,_kw/* Countries.countries806 */),
_kz/* countries64 */ = new T2(1,_ky/* Countries.countries805 */,_kv/* Countries.countries65 */),
_kA/* countries809 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominica"));
}),
_kB/* countries810 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DM"));
}),
_kC/* countries808 */ = new T2(0,_kB/* Countries.countries810 */,_kA/* Countries.countries809 */),
_kD/* countries63 */ = new T2(1,_kC/* Countries.countries808 */,_kz/* Countries.countries64 */),
_kE/* countries812 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Djibouti"));
}),
_kF/* countries813 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DJ"));
}),
_kG/* countries811 */ = new T2(0,_kF/* Countries.countries813 */,_kE/* Countries.countries812 */),
_kH/* countries62 */ = new T2(1,_kG/* Countries.countries811 */,_kD/* Countries.countries63 */),
_kI/* countries815 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Denmark"));
}),
_kJ/* countries816 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DK"));
}),
_kK/* countries814 */ = new T2(0,_kJ/* Countries.countries816 */,_kI/* Countries.countries815 */),
_kL/* countries61 */ = new T2(1,_kK/* Countries.countries814 */,_kH/* Countries.countries62 */),
_kM/* countries818 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Czech Republic"));
}),
_kN/* countries819 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CZ"));
}),
_kO/* countries817 */ = new T2(0,_kN/* Countries.countries819 */,_kM/* Countries.countries818 */),
_kP/* countries60 */ = new T2(1,_kO/* Countries.countries817 */,_kL/* Countries.countries61 */),
_kQ/* countries821 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cyprus"));
}),
_kR/* countries822 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CY"));
}),
_kS/* countries820 */ = new T2(0,_kR/* Countries.countries822 */,_kQ/* Countries.countries821 */),
_kT/* countries59 */ = new T2(1,_kS/* Countries.countries820 */,_kP/* Countries.countries60 */),
_kU/* countries824 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cura\u00e7ao"));
}),
_kV/* countries825 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CW"));
}),
_kW/* countries823 */ = new T2(0,_kV/* Countries.countries825 */,_kU/* Countries.countries824 */),
_kX/* countries58 */ = new T2(1,_kW/* Countries.countries823 */,_kT/* Countries.countries59 */),
_kY/* countries827 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cuba"));
}),
_kZ/* countries828 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CU"));
}),
_l0/* countries826 */ = new T2(0,_kZ/* Countries.countries828 */,_kY/* Countries.countries827 */),
_l1/* countries57 */ = new T2(1,_l0/* Countries.countries826 */,_kX/* Countries.countries58 */),
_l2/* countries830 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Croatia"));
}),
_l3/* countries831 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HR"));
}),
_l4/* countries829 */ = new T2(0,_l3/* Countries.countries831 */,_l2/* Countries.countries830 */),
_l5/* countries56 */ = new T2(1,_l4/* Countries.countries829 */,_l1/* Countries.countries57 */),
_l6/* countries833 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("C\u00f4te d\'Ivoire"));
}),
_l7/* countries834 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CI"));
}),
_l8/* countries832 */ = new T2(0,_l7/* Countries.countries834 */,_l6/* Countries.countries833 */),
_l9/* countries55 */ = new T2(1,_l8/* Countries.countries832 */,_l5/* Countries.countries56 */),
_la/* countries836 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Costa Rica"));
}),
_lb/* countries837 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_lc/* countries835 */ = new T2(0,_lb/* Countries.countries837 */,_la/* Countries.countries836 */),
_ld/* countries54 */ = new T2(1,_lc/* Countries.countries835 */,_l9/* Countries.countries55 */),
_le/* countries839 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cook Islands"));
}),
_lf/* countries840 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CK"));
}),
_lg/* countries838 */ = new T2(0,_lf/* Countries.countries840 */,_le/* Countries.countries839 */),
_lh/* countries53 */ = new T2(1,_lg/* Countries.countries838 */,_ld/* Countries.countries54 */),
_li/* countries842 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo, the Democratic Republic of the"));
}),
_lj/* countries843 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CD"));
}),
_lk/* countries841 */ = new T2(0,_lj/* Countries.countries843 */,_li/* Countries.countries842 */),
_ll/* countries52 */ = new T2(1,_lk/* Countries.countries841 */,_lh/* Countries.countries53 */),
_lm/* countries845 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo"));
}),
_ln/* countries846 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CG"));
}),
_lo/* countries844 */ = new T2(0,_ln/* Countries.countries846 */,_lm/* Countries.countries845 */),
_lp/* countries51 */ = new T2(1,_lo/* Countries.countries844 */,_ll/* Countries.countries52 */),
_lq/* countries848 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Comoros"));
}),
_lr/* countries849 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KM"));
}),
_ls/* countries847 */ = new T2(0,_lr/* Countries.countries849 */,_lq/* Countries.countries848 */),
_lt/* countries50 */ = new T2(1,_ls/* Countries.countries847 */,_lp/* Countries.countries51 */),
_lu/* countries851 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Colombia"));
}),
_lv/* countries852 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CO"));
}),
_lw/* countries850 */ = new T2(0,_lv/* Countries.countries852 */,_lu/* Countries.countries851 */),
_lx/* countries49 */ = new T2(1,_lw/* Countries.countries850 */,_lt/* Countries.countries50 */),
_ly/* countries854 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cocos (Keeling) Islands"));
}),
_lz/* countries855 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CC"));
}),
_lA/* countries853 */ = new T2(0,_lz/* Countries.countries855 */,_ly/* Countries.countries854 */),
_lB/* countries48 */ = new T2(1,_lA/* Countries.countries853 */,_lx/* Countries.countries49 */),
_lC/* countries857 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Christmas Island"));
}),
_lD/* countries858 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CX"));
}),
_lE/* countries856 */ = new T2(0,_lD/* Countries.countries858 */,_lC/* Countries.countries857 */),
_lF/* countries47 */ = new T2(1,_lE/* Countries.countries856 */,_lB/* Countries.countries48 */),
_lG/* countries860 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("China"));
}),
_lH/* countries861 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CN"));
}),
_lI/* countries859 */ = new T2(0,_lH/* Countries.countries861 */,_lG/* Countries.countries860 */),
_lJ/* countries46 */ = new T2(1,_lI/* Countries.countries859 */,_lF/* Countries.countries47 */),
_lK/* countries863 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chile"));
}),
_lL/* countries864 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CL"));
}),
_lM/* countries862 */ = new T2(0,_lL/* Countries.countries864 */,_lK/* Countries.countries863 */),
_lN/* countries45 */ = new T2(1,_lM/* Countries.countries862 */,_lJ/* Countries.countries46 */),
_lO/* countries866 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chad"));
}),
_lP/* countries867 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TD"));
}),
_lQ/* countries865 */ = new T2(0,_lP/* Countries.countries867 */,_lO/* Countries.countries866 */),
_lR/* countries44 */ = new T2(1,_lQ/* Countries.countries865 */,_lN/* Countries.countries45 */),
_lS/* countries869 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Central African Republic"));
}),
_lT/* countries870 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CF"));
}),
_lU/* countries868 */ = new T2(0,_lT/* Countries.countries870 */,_lS/* Countries.countries869 */),
_lV/* countries43 */ = new T2(1,_lU/* Countries.countries868 */,_lR/* Countries.countries44 */),
_lW/* countries872 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cayman Islands"));
}),
_lX/* countries873 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KY"));
}),
_lY/* countries871 */ = new T2(0,_lX/* Countries.countries873 */,_lW/* Countries.countries872 */),
_lZ/* countries42 */ = new T2(1,_lY/* Countries.countries871 */,_lV/* Countries.countries43 */),
_m0/* countries875 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cape Verde"));
}),
_m1/* countries876 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CV"));
}),
_m2/* countries874 */ = new T2(0,_m1/* Countries.countries876 */,_m0/* Countries.countries875 */),
_m3/* countries41 */ = new T2(1,_m2/* Countries.countries874 */,_lZ/* Countries.countries42 */),
_m4/* countries878 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canada"));
}),
_m5/* countries879 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CA"));
}),
_m6/* countries877 */ = new T2(0,_m5/* Countries.countries879 */,_m4/* Countries.countries878 */),
_m7/* countries40 */ = new T2(1,_m6/* Countries.countries877 */,_m3/* Countries.countries41 */),
_m8/* countries881 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cameroon"));
}),
_m9/* countries882 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CM"));
}),
_ma/* countries880 */ = new T2(0,_m9/* Countries.countries882 */,_m8/* Countries.countries881 */),
_mb/* countries39 */ = new T2(1,_ma/* Countries.countries880 */,_m7/* Countries.countries40 */),
_mc/* countries884 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cambodia"));
}),
_md/* countries885 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KH"));
}),
_me/* countries883 */ = new T2(0,_md/* Countries.countries885 */,_mc/* Countries.countries884 */),
_mf/* countries38 */ = new T2(1,_me/* Countries.countries883 */,_mb/* Countries.countries39 */),
_mg/* countries887 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burundi"));
}),
_mh/* countries888 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BI"));
}),
_mi/* countries886 */ = new T2(0,_mh/* Countries.countries888 */,_mg/* Countries.countries887 */),
_mj/* countries37 */ = new T2(1,_mi/* Countries.countries886 */,_mf/* Countries.countries38 */),
_mk/* countries890 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burkina Faso"));
}),
_ml/* countries891 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BF"));
}),
_mm/* countries889 */ = new T2(0,_ml/* Countries.countries891 */,_mk/* Countries.countries890 */),
_mn/* countries36 */ = new T2(1,_mm/* Countries.countries889 */,_mj/* Countries.countries37 */),
_mo/* countries893 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bulgaria"));
}),
_mp/* countries894 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BG"));
}),
_mq/* countries892 */ = new T2(0,_mp/* Countries.countries894 */,_mo/* Countries.countries893 */),
_mr/* countries35 */ = new T2(1,_mq/* Countries.countries892 */,_mn/* Countries.countries36 */),
_ms/* countries896 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brunei Darussalam"));
}),
_mt/* countries897 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BN"));
}),
_mu/* countries895 */ = new T2(0,_mt/* Countries.countries897 */,_ms/* Countries.countries896 */),
_mv/* countries34 */ = new T2(1,_mu/* Countries.countries895 */,_mr/* Countries.countries35 */),
_mw/* countries899 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("British Indian Ocean Territory"));
}),
_mx/* countries900 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IO"));
}),
_my/* countries898 */ = new T2(0,_mx/* Countries.countries900 */,_mw/* Countries.countries899 */),
_mz/* countries33 */ = new T2(1,_my/* Countries.countries898 */,_mv/* Countries.countries34 */),
_mA/* countries902 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brazil"));
}),
_mB/* countries903 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BR"));
}),
_mC/* countries901 */ = new T2(0,_mB/* Countries.countries903 */,_mA/* Countries.countries902 */),
_mD/* countries32 */ = new T2(1,_mC/* Countries.countries901 */,_mz/* Countries.countries33 */),
_mE/* countries905 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bouvet Island"));
}),
_mF/* countries906 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BV"));
}),
_mG/* countries904 */ = new T2(0,_mF/* Countries.countries906 */,_mE/* Countries.countries905 */),
_mH/* countries31 */ = new T2(1,_mG/* Countries.countries904 */,_mD/* Countries.countries32 */),
_mI/* countries908 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Botswana"));
}),
_mJ/* countries909 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BW"));
}),
_mK/* countries907 */ = new T2(0,_mJ/* Countries.countries909 */,_mI/* Countries.countries908 */),
_mL/* countries30 */ = new T2(1,_mK/* Countries.countries907 */,_mH/* Countries.countries31 */),
_mM/* countries911 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bosnia and Herzegovina"));
}),
_mN/* countries912 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BA"));
}),
_mO/* countries910 */ = new T2(0,_mN/* Countries.countries912 */,_mM/* Countries.countries911 */),
_mP/* countries29 */ = new T2(1,_mO/* Countries.countries910 */,_mL/* Countries.countries30 */),
_mQ/* countries914 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bonaire, Sint Eustatius and Saba"));
}),
_mR/* countries915 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BQ"));
}),
_mS/* countries913 */ = new T2(0,_mR/* Countries.countries915 */,_mQ/* Countries.countries914 */),
_mT/* countries28 */ = new T2(1,_mS/* Countries.countries913 */,_mP/* Countries.countries29 */),
_mU/* countries917 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bolivia, Plurinational State of"));
}),
_mV/* countries918 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BO"));
}),
_mW/* countries916 */ = new T2(0,_mV/* Countries.countries918 */,_mU/* Countries.countries917 */),
_mX/* countries27 */ = new T2(1,_mW/* Countries.countries916 */,_mT/* Countries.countries28 */),
_mY/* countries920 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bhutan"));
}),
_mZ/* countries921 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BT"));
}),
_n0/* countries919 */ = new T2(0,_mZ/* Countries.countries921 */,_mY/* Countries.countries920 */),
_n1/* countries26 */ = new T2(1,_n0/* Countries.countries919 */,_mX/* Countries.countries27 */),
_n2/* countries923 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bermuda"));
}),
_n3/* countries924 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BM"));
}),
_n4/* countries922 */ = new T2(0,_n3/* Countries.countries924 */,_n2/* Countries.countries923 */),
_n5/* countries25 */ = new T2(1,_n4/* Countries.countries922 */,_n1/* Countries.countries26 */),
_n6/* countries926 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Benin"));
}),
_n7/* countries927 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BJ"));
}),
_n8/* countries925 */ = new T2(0,_n7/* Countries.countries927 */,_n6/* Countries.countries926 */),
_n9/* countries24 */ = new T2(1,_n8/* Countries.countries925 */,_n5/* Countries.countries25 */),
_na/* countries929 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belize"));
}),
_nb/* countries930 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BZ"));
}),
_nc/* countries928 */ = new T2(0,_nb/* Countries.countries930 */,_na/* Countries.countries929 */),
_nd/* countries23 */ = new T2(1,_nc/* Countries.countries928 */,_n9/* Countries.countries24 */),
_ne/* countries932 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belgium"));
}),
_nf/* countries933 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BE"));
}),
_ng/* countries931 */ = new T2(0,_nf/* Countries.countries933 */,_ne/* Countries.countries932 */),
_nh/* countries22 */ = new T2(1,_ng/* Countries.countries931 */,_nd/* Countries.countries23 */),
_ni/* countries935 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belarus"));
}),
_nj/* countries936 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BY"));
}),
_nk/* countries934 */ = new T2(0,_nj/* Countries.countries936 */,_ni/* Countries.countries935 */),
_nl/* countries21 */ = new T2(1,_nk/* Countries.countries934 */,_nh/* Countries.countries22 */),
_nm/* countries938 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Barbados"));
}),
_nn/* countries939 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BB"));
}),
_no/* countries937 */ = new T2(0,_nn/* Countries.countries939 */,_nm/* Countries.countries938 */),
_np/* countries20 */ = new T2(1,_no/* Countries.countries937 */,_nl/* Countries.countries21 */),
_nq/* countries941 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bangladesh"));
}),
_nr/* countries942 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BD"));
}),
_ns/* countries940 */ = new T2(0,_nr/* Countries.countries942 */,_nq/* Countries.countries941 */),
_nt/* countries19 */ = new T2(1,_ns/* Countries.countries940 */,_np/* Countries.countries20 */),
_nu/* countries944 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahrain"));
}),
_nv/* countries945 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BH"));
}),
_nw/* countries943 */ = new T2(0,_nv/* Countries.countries945 */,_nu/* Countries.countries944 */),
_nx/* countries18 */ = new T2(1,_nw/* Countries.countries943 */,_nt/* Countries.countries19 */),
_ny/* countries947 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahamas"));
}),
_nz/* countries948 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_nA/* countries946 */ = new T2(0,_nz/* Countries.countries948 */,_ny/* Countries.countries947 */),
_nB/* countries17 */ = new T2(1,_nA/* Countries.countries946 */,_nx/* Countries.countries18 */),
_nC/* countries950 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Azerbaijan"));
}),
_nD/* countries951 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AZ"));
}),
_nE/* countries949 */ = new T2(0,_nD/* Countries.countries951 */,_nC/* Countries.countries950 */),
_nF/* countries16 */ = new T2(1,_nE/* Countries.countries949 */,_nB/* Countries.countries17 */),
_nG/* countries953 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Austria"));
}),
_nH/* countries954 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AT"));
}),
_nI/* countries952 */ = new T2(0,_nH/* Countries.countries954 */,_nG/* Countries.countries953 */),
_nJ/* countries15 */ = new T2(1,_nI/* Countries.countries952 */,_nF/* Countries.countries16 */),
_nK/* countries956 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Australia"));
}),
_nL/* countries957 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AU"));
}),
_nM/* countries955 */ = new T2(0,_nL/* Countries.countries957 */,_nK/* Countries.countries956 */),
_nN/* countries14 */ = new T2(1,_nM/* Countries.countries955 */,_nJ/* Countries.countries15 */),
_nO/* countries959 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Aruba"));
}),
_nP/* countries960 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AW"));
}),
_nQ/* countries958 */ = new T2(0,_nP/* Countries.countries960 */,_nO/* Countries.countries959 */),
_nR/* countries13 */ = new T2(1,_nQ/* Countries.countries958 */,_nN/* Countries.countries14 */),
_nS/* countries962 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Armenia"));
}),
_nT/* countries963 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AM"));
}),
_nU/* countries961 */ = new T2(0,_nT/* Countries.countries963 */,_nS/* Countries.countries962 */),
_nV/* countries12 */ = new T2(1,_nU/* Countries.countries961 */,_nR/* Countries.countries13 */),
_nW/* countries965 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Argentina"));
}),
_nX/* countries966 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AR"));
}),
_nY/* countries964 */ = new T2(0,_nX/* Countries.countries966 */,_nW/* Countries.countries965 */),
_nZ/* countries11 */ = new T2(1,_nY/* Countries.countries964 */,_nV/* Countries.countries12 */),
_o0/* countries968 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antigua and Barbuda"));
}),
_o1/* countries969 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AG"));
}),
_o2/* countries967 */ = new T2(0,_o1/* Countries.countries969 */,_o0/* Countries.countries968 */),
_o3/* countries10 */ = new T2(1,_o2/* Countries.countries967 */,_nZ/* Countries.countries11 */),
_o4/* countries971 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antarctica"));
}),
_o5/* countries972 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AQ"));
}),
_o6/* countries970 */ = new T2(0,_o5/* Countries.countries972 */,_o4/* Countries.countries971 */),
_o7/* countries9 */ = new T2(1,_o6/* Countries.countries970 */,_o3/* Countries.countries10 */),
_o8/* countries974 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Anguilla"));
}),
_o9/* countries975 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AI"));
}),
_oa/* countries973 */ = new T2(0,_o9/* Countries.countries975 */,_o8/* Countries.countries974 */),
_ob/* countries8 */ = new T2(1,_oa/* Countries.countries973 */,_o7/* Countries.countries9 */),
_oc/* countries977 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Angola"));
}),
_od/* countries978 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AO"));
}),
_oe/* countries976 */ = new T2(0,_od/* Countries.countries978 */,_oc/* Countries.countries977 */),
_of/* countries7 */ = new T2(1,_oe/* Countries.countries976 */,_ob/* Countries.countries8 */),
_og/* countries980 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Andorra"));
}),
_oh/* countries981 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AD"));
}),
_oi/* countries979 */ = new T2(0,_oh/* Countries.countries981 */,_og/* Countries.countries980 */),
_oj/* countries6 */ = new T2(1,_oi/* Countries.countries979 */,_of/* Countries.countries7 */),
_ok/* countries983 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("American Samoa"));
}),
_ol/* countries984 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AS"));
}),
_om/* countries982 */ = new T2(0,_ol/* Countries.countries984 */,_ok/* Countries.countries983 */),
_on/* countries5 */ = new T2(1,_om/* Countries.countries982 */,_oj/* Countries.countries6 */),
_oo/* countries986 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Algeria"));
}),
_op/* countries987 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DZ"));
}),
_oq/* countries985 */ = new T2(0,_op/* Countries.countries987 */,_oo/* Countries.countries986 */),
_or/* countries4 */ = new T2(1,_oq/* Countries.countries985 */,_on/* Countries.countries5 */),
_os/* countries989 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Albania"));
}),
_ot/* countries990 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AL"));
}),
_ou/* countries988 */ = new T2(0,_ot/* Countries.countries990 */,_os/* Countries.countries989 */),
_ov/* countries3 */ = new T2(1,_ou/* Countries.countries988 */,_or/* Countries.countries4 */),
_ow/* countries992 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u00c5land Islands"));
}),
_ox/* countries993 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AX"));
}),
_oy/* countries991 */ = new T2(0,_ox/* Countries.countries993 */,_ow/* Countries.countries992 */),
_oz/* countries2 */ = new T2(1,_oy/* Countries.countries991 */,_ov/* Countries.countries3 */),
_oA/* countries995 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Afghanistan"));
}),
_oB/* countries996 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AF"));
}),
_oC/* countries994 */ = new T2(0,_oB/* Countries.countries996 */,_oA/* Countries.countries995 */),
_oD/* countries1 */ = new T2(1,_oC/* Countries.countries994 */,_oz/* Countries.countries2 */),
_oE/* countries998 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("--select--"));
}),
_oF/* countries997 */ = new T2(0,_I/* GHC.Types.[] */,_oE/* Countries.countries998 */),
_oG/* countries */ = new T2(1,_oF/* Countries.countries997 */,_oD/* Countries.countries1 */),
_oH/* ch0GeneralInformation33 */ = new T2(6,_8z/* FormStructure.Chapter0.ch0GeneralInformation34 */,_oG/* Countries.countries */),
_oI/* ch0GeneralInformation32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institution name"));
}),
_oJ/* ch0GeneralInformation31 */ = new T1(1,_oI/* FormStructure.Chapter0.ch0GeneralInformation32 */),
_oK/* ch0GeneralInformation30 */ = {_:0,a:_oJ/* FormStructure.Chapter0.ch0GeneralInformation31 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_oL/* ch0GeneralInformation29 */ = new T1(0,_oK/* FormStructure.Chapter0.ch0GeneralInformation30 */),
_oM/* ch0GeneralInformation28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Organisation unit"));
}),
_oN/* ch0GeneralInformation27 */ = new T1(1,_oM/* FormStructure.Chapter0.ch0GeneralInformation28 */),
_oO/* ch0GeneralInformation26 */ = {_:0,a:_oN/* FormStructure.Chapter0.ch0GeneralInformation27 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_oP/* ch0GeneralInformation25 */ = new T1(0,_oO/* FormStructure.Chapter0.ch0GeneralInformation26 */),
_oQ/* ch0GeneralInformation15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("research group"));
}),
_oR/* ch0GeneralInformation14 */ = new T1(0,_oQ/* FormStructure.Chapter0.ch0GeneralInformation15 */),
_oS/* ch0GeneralInformation13 */ = new T2(1,_oR/* FormStructure.Chapter0.ch0GeneralInformation14 */,_I/* GHC.Types.[] */),
_oT/* ch0GeneralInformation17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("department"));
}),
_oU/* ch0GeneralInformation16 */ = new T1(0,_oT/* FormStructure.Chapter0.ch0GeneralInformation17 */),
_oV/* ch0GeneralInformation12 */ = new T2(1,_oU/* FormStructure.Chapter0.ch0GeneralInformation16 */,_oS/* FormStructure.Chapter0.ch0GeneralInformation13 */),
_oW/* ch0GeneralInformation19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("faculty"));
}),
_oX/* ch0GeneralInformation18 */ = new T1(0,_oW/* FormStructure.Chapter0.ch0GeneralInformation19 */),
_oY/* ch0GeneralInformation11 */ = new T2(1,_oX/* FormStructure.Chapter0.ch0GeneralInformation18 */,_oV/* FormStructure.Chapter0.ch0GeneralInformation12 */),
_oZ/* ch0GeneralInformation21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution"));
}),
_p0/* ch0GeneralInformation20 */ = new T1(0,_oZ/* FormStructure.Chapter0.ch0GeneralInformation21 */),
_p1/* ch0GeneralInformation10 */ = new T2(1,_p0/* FormStructure.Chapter0.ch0GeneralInformation20 */,_oY/* FormStructure.Chapter0.ch0GeneralInformation11 */),
_p2/* ch0GeneralInformation24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Level of unit"));
}),
_p3/* ch0GeneralInformation23 */ = new T1(1,_p2/* FormStructure.Chapter0.ch0GeneralInformation24 */),
_p4/* ch0GeneralInformation22 */ = {_:0,a:_p3/* FormStructure.Chapter0.ch0GeneralInformation23 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_p5/* ch0GeneralInformation9 */ = new T2(5,_p4/* FormStructure.Chapter0.ch0GeneralInformation22 */,_p1/* FormStructure.Chapter0.ch0GeneralInformation10 */),
_p6/* ch0GeneralInformation8 */ = new T2(1,_p5/* FormStructure.Chapter0.ch0GeneralInformation9 */,_I/* GHC.Types.[] */),
_p7/* ch0GeneralInformation7 */ = new T2(1,_oP/* FormStructure.Chapter0.ch0GeneralInformation25 */,_p6/* FormStructure.Chapter0.ch0GeneralInformation8 */),
_p8/* ch0GeneralInformation6 */ = new T2(1,_oL/* FormStructure.Chapter0.ch0GeneralInformation29 */,_p7/* FormStructure.Chapter0.ch0GeneralInformation7 */),
_p9/* ch0GeneralInformation5 */ = new T2(1,_oH/* FormStructure.Chapter0.ch0GeneralInformation33 */,_p8/* FormStructure.Chapter0.ch0GeneralInformation6 */),
_pa/* ch0GeneralInformation4 */ = new T3(8,_8w/* FormStructure.Chapter0.ch0GeneralInformation38 */,_8t/* FormStructure.Chapter0.ch0GeneralInformation37 */,_p9/* FormStructure.Chapter0.ch0GeneralInformation5 */),
_pb/* ch0GeneralInformation2 */ = new T2(1,_pa/* FormStructure.Chapter0.ch0GeneralInformation4 */,_8s/* FormStructure.Chapter0.ch0GeneralInformation3 */),
_pc/* ch0GeneralInformation48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Email"));
}),
_pd/* ch0GeneralInformation47 */ = new T1(1,_pc/* FormStructure.Chapter0.ch0GeneralInformation48 */),
_pe/* ch0GeneralInformation46 */ = {_:0,a:_pd/* FormStructure.Chapter0.ch0GeneralInformation47 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pf/* ch0GeneralInformation45 */ = new T1(2,_pe/* FormStructure.Chapter0.ch0GeneralInformation46 */),
_pg/* ch0GeneralInformation44 */ = new T2(1,_pf/* FormStructure.Chapter0.ch0GeneralInformation45 */,_I/* GHC.Types.[] */),
_ph/* ch0GeneralInformation52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Surname"));
}),
_pi/* ch0GeneralInformation51 */ = new T1(1,_ph/* FormStructure.Chapter0.ch0GeneralInformation52 */),
_pj/* ch0GeneralInformation50 */ = {_:0,a:_pi/* FormStructure.Chapter0.ch0GeneralInformation51 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pk/* ch0GeneralInformation49 */ = new T1(0,_pj/* FormStructure.Chapter0.ch0GeneralInformation50 */),
_pl/* ch0GeneralInformation43 */ = new T2(1,_pk/* FormStructure.Chapter0.ch0GeneralInformation49 */,_pg/* FormStructure.Chapter0.ch0GeneralInformation44 */),
_pm/* ch0GeneralInformation56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("First name"));
}),
_pn/* ch0GeneralInformation55 */ = new T1(1,_pm/* FormStructure.Chapter0.ch0GeneralInformation56 */),
_po/* ch0GeneralInformation54 */ = {_:0,a:_pn/* FormStructure.Chapter0.ch0GeneralInformation55 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_pp/* ch0GeneralInformation53 */ = new T1(0,_po/* FormStructure.Chapter0.ch0GeneralInformation54 */),
_pq/* ch0GeneralInformation42 */ = new T2(1,_pp/* FormStructure.Chapter0.ch0GeneralInformation53 */,_pl/* FormStructure.Chapter0.ch0GeneralInformation43 */),
_pr/* ch0GeneralInformation59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Registration of the responder"));
}),
_ps/* ch0GeneralInformation58 */ = new T1(1,_pr/* FormStructure.Chapter0.ch0GeneralInformation59 */),
_pt/* ch0GeneralInformation57 */ = {_:0,a:_ps/* FormStructure.Chapter0.ch0GeneralInformation58 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pu/* ch0GeneralInformation41 */ = new T3(8,_pt/* FormStructure.Chapter0.ch0GeneralInformation57 */,_8t/* FormStructure.Chapter0.ch0GeneralInformation37 */,_pq/* FormStructure.Chapter0.ch0GeneralInformation42 */),
_pv/* ch0GeneralInformation1 */ = new T2(1,_pu/* FormStructure.Chapter0.ch0GeneralInformation41 */,_pb/* FormStructure.Chapter0.ch0GeneralInformation2 */),
_pw/* ch0GeneralInformation62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("0.General Info"));
}),
_px/* ch0GeneralInformation61 */ = new T1(1,_pw/* FormStructure.Chapter0.ch0GeneralInformation62 */),
_py/* ch0GeneralInformation60 */ = {_:0,a:_px/* FormStructure.Chapter0.ch0GeneralInformation61 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_pz/* ch0GeneralInformation */ = new T2(7,_py/* FormStructure.Chapter0.ch0GeneralInformation60 */,_pv/* FormStructure.Chapter0.ch0GeneralInformation1 */),
_pA/* ch1DataProduction226 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you produce raw data?"));
}),
_pB/* ch1DataProduction225 */ = new T1(1,_pA/* FormStructure.Chapter1.ch1DataProduction226 */),
_pC/* ch1DataProduction224 */ = {_:0,a:_pB/* FormStructure.Chapter1.ch1DataProduction225 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pD/* ch1DataProduction6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_pE/* ch1DataProduction5 */ = new T1(0,_pD/* FormStructure.Chapter1.ch1DataProduction6 */),
_pF/* ch1DataProduction4 */ = new T2(1,_pE/* FormStructure.Chapter1.ch1DataProduction5 */,_I/* GHC.Types.[] */),
_pG/* ch1DataProduction223 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_pH/* ch1DataProduction123 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_pI/* ch1DataProduction122 */ = new T1(0,_pH/* FormStructure.Chapter1.ch1DataProduction123 */),
_pJ/* ReadOnlyRule */ = new T0(3),
_pK/* ch1DataProduction125 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_pL/* ch1DataProduction127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-sum"));
}),
_pM/* ch1DataProduction126 */ = new T1(1,_pL/* FormStructure.Chapter1.ch1DataProduction127 */),
_pN/* ch1DataProduction129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production cost"));
}),
_pO/* ch1DataProduction128 */ = new T1(1,_pN/* FormStructure.Chapter1.ch1DataProduction129 */),
_pP/* ch1DataProduction124 */ = {_:0,a:_pO/* FormStructure.Chapter1.ch1DataProduction128 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_pM/* FormStructure.Chapter1.ch1DataProduction126 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_pK/* FormStructure.Chapter1.ch1DataProduction125 */},
_pQ/* ch1DataProduction121 */ = new T2(3,_pP/* FormStructure.Chapter1.ch1DataProduction124 */,_pI/* FormStructure.Chapter1.ch1DataProduction122 */),
_pR/* ch1DataProduction120 */ = new T2(1,_pQ/* FormStructure.Chapter1.ch1DataProduction121 */,_I/* GHC.Types.[] */),
_pS/* ch1DataProduction132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_pT/* ch1DataProduction131 */ = new T1(0,_pS/* FormStructure.Chapter1.ch1DataProduction132 */),
_pU/* totalSum1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_pV/* totalSum11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_pW/* totalSum10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_pX/* totalSum7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_pY/* totalSum6 */ = new T2(1,_pX/* FormStructure.Common.totalSum7 */,_I/* GHC.Types.[] */),
_pZ/* totalSum8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_q0/* totalSum5 */ = new T2(1,_pZ/* FormStructure.Common.totalSum8 */,_pY/* FormStructure.Common.totalSum6 */),
_q1/* totalSum9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_q2/* totalSum4 */ = new T2(1,_q1/* FormStructure.Common.totalSum9 */,_q0/* FormStructure.Common.totalSum5 */),
_q3/* totalSum3 */ = new T2(1,_pW/* FormStructure.Common.totalSum10 */,_q2/* FormStructure.Common.totalSum4 */),
_q4/* totalSum2 */ = new T2(1,_pV/* FormStructure.Common.totalSum11 */,_q3/* FormStructure.Common.totalSum3 */),
_q5/* totalSum */ = new T2(1,_q4/* FormStructure.Common.totalSum2 */,_pU/* FormStructure.Common.totalSum1 */),
_q6/* ch1DataProduction135 */ = new T2(1,_q5/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_q7/* ch1DataProduction134 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_q6/* FormStructure.Chapter1.ch1DataProduction135 */),
_q8/* ch1DataProduction137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-sum"));
}),
_q9/* ch1DataProduction136 */ = new T1(1,_q8/* FormStructure.Chapter1.ch1DataProduction137 */),
_qa/* ch1DataProduction139 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production volume"));
}),
_qb/* ch1DataProduction138 */ = new T1(1,_qa/* FormStructure.Chapter1.ch1DataProduction139 */),
_qc/* ch1DataProduction133 */ = {_:0,a:_qb/* FormStructure.Chapter1.ch1DataProduction138 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_q9/* FormStructure.Chapter1.ch1DataProduction136 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_q7/* FormStructure.Chapter1.ch1DataProduction134 */},
_qd/* ch1DataProduction130 */ = new T2(3,_qc/* FormStructure.Chapter1.ch1DataProduction133 */,_pT/* FormStructure.Chapter1.ch1DataProduction131 */),
_qe/* ch1DataProduction119 */ = new T2(1,_qd/* FormStructure.Chapter1.ch1DataProduction130 */,_pR/* FormStructure.Chapter1.ch1DataProduction120 */),
_qf/* ch1DataProduction150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-others"));
}),
_qg/* ch1DataProduction149 */ = new T2(1,_qf/* FormStructure.Chapter1.ch1DataProduction150 */,_I/* GHC.Types.[] */),
_qh/* ch1DataProduction151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-proteomics"));
}),
_qi/* ch1DataProduction148 */ = new T2(1,_qh/* FormStructure.Chapter1.ch1DataProduction151 */,_qg/* FormStructure.Chapter1.ch1DataProduction149 */),
_qj/* ch1DataProduction152 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-genomics"));
}),
_qk/* ch1DataProduction147 */ = new T2(1,_qj/* FormStructure.Chapter1.ch1DataProduction152 */,_qi/* FormStructure.Chapter1.ch1DataProduction148 */),
_ql/* ch1DataProduction_costSumRule */ = new T2(0,_qk/* FormStructure.Chapter1.ch1DataProduction147 */,_pL/* FormStructure.Chapter1.ch1DataProduction127 */),
_qm/* ch1DataProduction146 */ = new T2(1,_ql/* FormStructure.Chapter1.ch1DataProduction_costSumRule */,_I/* GHC.Types.[] */),
_qn/* ch1DataProduction154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_qo/* ch1DataProduction153 */ = new T1(1,_qn/* FormStructure.Chapter1.ch1DataProduction154 */),
_qp/* ch1DataProduction155 */ = new T1(1,_qf/* FormStructure.Chapter1.ch1DataProduction150 */),
_qq/* ch1DataProduction157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost for year 2015"));
}),
_qr/* ch1DataProduction156 */ = new T1(1,_qq/* FormStructure.Chapter1.ch1DataProduction157 */),
_qs/* ch1DataProduction145 */ = {_:0,a:_qr/* FormStructure.Chapter1.ch1DataProduction156 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_qp/* FormStructure.Chapter1.ch1DataProduction155 */,d:_I/* GHC.Types.[] */,e:_qo/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qm/* FormStructure.Chapter1.ch1DataProduction146 */},
_qt/* ch1DataProduction144 */ = new T2(3,_qs/* FormStructure.Chapter1.ch1DataProduction145 */,_pI/* FormStructure.Chapter1.ch1DataProduction122 */),
_qu/* ch1DataProduction143 */ = new T2(1,_qt/* FormStructure.Chapter1.ch1DataProduction144 */,_I/* GHC.Types.[] */),
_qv/* ch1DataProduction164 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_qw/* ch1DataProduction163 */ = new T2(1,_qv/* FormStructure.Chapter1.ch1DataProduction164 */,_I/* GHC.Types.[] */),
_qx/* ch1DataProduction162 */ = new T2(1,_pS/* FormStructure.Chapter1.ch1DataProduction132 */,_qw/* FormStructure.Chapter1.ch1DataProduction163 */),
_qy/* ch1DataProduction165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_qz/* ch1DataProduction161 */ = new T2(1,_qy/* FormStructure.Chapter1.ch1DataProduction165 */,_qx/* FormStructure.Chapter1.ch1DataProduction162 */),
_qA/* ch1DataProduction166 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_qB/* ch1DataProduction160 */ = new T2(1,_qA/* FormStructure.Chapter1.ch1DataProduction166 */,_qz/* FormStructure.Chapter1.ch1DataProduction161 */),
_qC/* ch1DataProduction159 */ = new T1(1,_qB/* FormStructure.Chapter1.ch1DataProduction160 */),
_qD/* ch1DataProduction180 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_qE/* ch1DataProduction179 */ = new T2(1,_qD/* FormStructure.Chapter1.ch1DataProduction180 */,_I/* GHC.Types.[] */),
_qF/* ch1DataProduction181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_qG/* ch1DataProduction178 */ = new T2(1,_qF/* FormStructure.Chapter1.ch1DataProduction181 */,_qE/* FormStructure.Chapter1.ch1DataProduction179 */),
_qH/* ch1DataProduction175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_qI/* ch1DataProduction182 */ = new T1(1,_qH/* FormStructure.Chapter1.ch1DataProduction175 */),
_qJ/* ch1DataProduction184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Volume"));
}),
_qK/* ch1DataProduction183 */ = new T1(1,_qJ/* FormStructure.Chapter1.ch1DataProduction184 */),
_qL/* ch1DataProduction170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_qM/* ch1DataProduction169 */ = new T2(2,_q8/* FormStructure.Chapter1.ch1DataProduction137 */,_qL/* FormStructure.Chapter1.ch1DataProduction170 */),
_qN/* ch1DataProduction168 */ = new T2(1,_qM/* FormStructure.Chapter1.ch1DataProduction169 */,_I/* GHC.Types.[] */),
_qO/* ch1DataProduction174 */ = new T2(1,_qH/* FormStructure.Chapter1.ch1DataProduction175 */,_I/* GHC.Types.[] */),
_qP/* ch1DataProduction176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_qQ/* ch1DataProduction173 */ = new T2(1,_qP/* FormStructure.Chapter1.ch1DataProduction176 */,_qO/* FormStructure.Chapter1.ch1DataProduction174 */),
_qR/* ch1DataProduction177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_qS/* ch1DataProduction172 */ = new T2(1,_qR/* FormStructure.Chapter1.ch1DataProduction177 */,_qQ/* FormStructure.Chapter1.ch1DataProduction173 */),
_qT/* ch1DataProduction171 */ = new T2(1,_qS/* FormStructure.Chapter1.ch1DataProduction172 */,_q8/* FormStructure.Chapter1.ch1DataProduction137 */),
_qU/* ch1DataProduction_volumeSumRules */ = new T2(1,_qT/* FormStructure.Chapter1.ch1DataProduction171 */,_qN/* FormStructure.Chapter1.ch1DataProduction168 */),
_qV/* ch1DataProduction167 */ = {_:0,a:_qK/* FormStructure.Chapter1.ch1DataProduction183 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_qI/* FormStructure.Chapter1.ch1DataProduction182 */,d:_qG/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_qU/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_qW/* ch1DataProduction158 */ = new T2(3,_qV/* FormStructure.Chapter1.ch1DataProduction167 */,_qC/* FormStructure.Chapter1.ch1DataProduction159 */),
_qX/* ch1DataProduction142 */ = new T2(1,_qW/* FormStructure.Chapter1.ch1DataProduction158 */,_qu/* FormStructure.Chapter1.ch1DataProduction143 */),
_qY/* ch1DataProduction188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Images, chips, spectra, ..."));
}),
_qZ/* ch1DataProduction187 */ = new T1(1,_qY/* FormStructure.Chapter1.ch1DataProduction188 */),
_r0/* ch1DataProduction190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Specify the output type of raw data"));
}),
_r1/* ch1DataProduction189 */ = new T1(1,_r0/* FormStructure.Chapter1.ch1DataProduction190 */),
_r2/* ch1DataProduction186 */ = {_:0,a:_r1/* FormStructure.Chapter1.ch1DataProduction189 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_qZ/* FormStructure.Chapter1.ch1DataProduction187 */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_r3/* ch1DataProduction185 */ = new T1(0,_r2/* FormStructure.Chapter1.ch1DataProduction186 */),
_r4/* ch1DataProduction141 */ = new T2(1,_r3/* FormStructure.Chapter1.ch1DataProduction185 */,_qX/* FormStructure.Chapter1.ch1DataProduction142 */),
_r5/* ch1DataProduction193 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Others"));
}),
_r6/* ch1DataProduction192 */ = new T1(1,_r5/* FormStructure.Chapter1.ch1DataProduction193 */),
_r7/* ch1DataProduction191 */ = {_:0,a:_r6/* FormStructure.Chapter1.ch1DataProduction192 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_r8/* ch1DataProduction67 */ = 0,
_r9/* ch1DataProduction140 */ = new T3(9,_r7/* FormStructure.Chapter1.ch1DataProduction191 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_r4/* FormStructure.Chapter1.ch1DataProduction141 */),
_ra/* ch1DataProduction118 */ = new T2(1,_r9/* FormStructure.Chapter1.ch1DataProduction140 */,_qe/* FormStructure.Chapter1.ch1DataProduction119 */),
_rb/* ch1DataProduction199 */ = new T1(1,_qh/* FormStructure.Chapter1.ch1DataProduction151 */),
_rc/* ch1DataProduction198 */ = {_:0,a:_qr/* FormStructure.Chapter1.ch1DataProduction156 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_rb/* FormStructure.Chapter1.ch1DataProduction199 */,d:_I/* GHC.Types.[] */,e:_qo/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qm/* FormStructure.Chapter1.ch1DataProduction146 */},
_rd/* ch1DataProduction197 */ = new T2(3,_rc/* FormStructure.Chapter1.ch1DataProduction198 */,_pI/* FormStructure.Chapter1.ch1DataProduction122 */),
_re/* ch1DataProduction196 */ = new T2(1,_rd/* FormStructure.Chapter1.ch1DataProduction197 */,_I/* GHC.Types.[] */),
_rf/* ch1DataProduction202 */ = new T1(1,_qP/* FormStructure.Chapter1.ch1DataProduction176 */),
_rg/* ch1DataProduction201 */ = {_:0,a:_qK/* FormStructure.Chapter1.ch1DataProduction183 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_rf/* FormStructure.Chapter1.ch1DataProduction202 */,d:_qG/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_qU/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_rh/* ch1DataProduction200 */ = new T2(3,_rg/* FormStructure.Chapter1.ch1DataProduction201 */,_qC/* FormStructure.Chapter1.ch1DataProduction159 */),
_ri/* ch1DataProduction195 */ = new T2(1,_rh/* FormStructure.Chapter1.ch1DataProduction200 */,_re/* FormStructure.Chapter1.ch1DataProduction196 */),
_rj/* ch1DataProduction205 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Proteomics"));
}),
_rk/* ch1DataProduction204 */ = new T1(1,_rj/* FormStructure.Chapter1.ch1DataProduction205 */),
_rl/* ch1DataProduction203 */ = {_:0,a:_rk/* FormStructure.Chapter1.ch1DataProduction204 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rm/* ch1DataProduction194 */ = new T3(9,_rl/* FormStructure.Chapter1.ch1DataProduction203 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_ri/* FormStructure.Chapter1.ch1DataProduction195 */),
_rn/* ch1DataProduction117 */ = new T2(1,_rm/* FormStructure.Chapter1.ch1DataProduction194 */,_ra/* FormStructure.Chapter1.ch1DataProduction118 */),
_ro/* ch1DataProduction211 */ = new T1(1,_qj/* FormStructure.Chapter1.ch1DataProduction152 */),
_rp/* ch1DataProduction210 */ = {_:0,a:_qr/* FormStructure.Chapter1.ch1DataProduction156 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_ro/* FormStructure.Chapter1.ch1DataProduction211 */,d:_I/* GHC.Types.[] */,e:_qo/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qm/* FormStructure.Chapter1.ch1DataProduction146 */},
_rq/* ch1DataProduction209 */ = new T2(3,_rp/* FormStructure.Chapter1.ch1DataProduction210 */,_pI/* FormStructure.Chapter1.ch1DataProduction122 */),
_rr/* ch1DataProduction208 */ = new T2(1,_rq/* FormStructure.Chapter1.ch1DataProduction209 */,_I/* GHC.Types.[] */),
_rs/* ch1DataProduction214 */ = new T1(1,_qR/* FormStructure.Chapter1.ch1DataProduction177 */),
_rt/* ch1DataProduction213 */ = {_:0,a:_qK/* FormStructure.Chapter1.ch1DataProduction183 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_rs/* FormStructure.Chapter1.ch1DataProduction214 */,d:_qG/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_qU/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_ru/* ch1DataProduction212 */ = new T2(3,_rt/* FormStructure.Chapter1.ch1DataProduction213 */,_qC/* FormStructure.Chapter1.ch1DataProduction159 */),
_rv/* ch1DataProduction207 */ = new T2(1,_ru/* FormStructure.Chapter1.ch1DataProduction212 */,_rr/* FormStructure.Chapter1.ch1DataProduction208 */),
_rw/* ch1DataProduction217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Genomics"));
}),
_rx/* ch1DataProduction216 */ = new T1(1,_rw/* FormStructure.Chapter1.ch1DataProduction217 */),
_ry/* ch1DataProduction215 */ = {_:0,a:_rx/* FormStructure.Chapter1.ch1DataProduction216 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rz/* ch1DataProduction206 */ = new T3(9,_ry/* FormStructure.Chapter1.ch1DataProduction215 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_rv/* FormStructure.Chapter1.ch1DataProduction207 */),
_rA/* ch1DataProduction116 */ = new T2(1,_rz/* FormStructure.Chapter1.ch1DataProduction206 */,_rn/* FormStructure.Chapter1.ch1DataProduction117 */),
_rB/* ch1DataProduction220 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(Estimated) volume of raw data produced inhouse in 2015"));
}),
_rC/* ch1DataProduction219 */ = new T1(1,_rB/* FormStructure.Chapter1.ch1DataProduction220 */),
_rD/* ch1DataProduction222 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Type of data"));
}),
_rE/* ch1DataProduction221 */ = new T1(1,_rD/* FormStructure.Chapter1.ch1DataProduction222 */),
_rF/* ch1DataProduction218 */ = {_:0,a:_rE/* FormStructure.Chapter1.ch1DataProduction221 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_rC/* FormStructure.Chapter1.ch1DataProduction219 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rG/* ch1DataProduction115 */ = new T3(8,_rF/* FormStructure.Chapter1.ch1DataProduction218 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_rA/* FormStructure.Chapter1.ch1DataProduction116 */),
_rH/* ch1DataProduction11 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_rI/* ch1DataProduction19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_rJ/* ch1DataProduction18 */ = new T1(0,_rI/* FormStructure.Chapter1.ch1DataProduction19 */),
_rK/* ch1DataProduction24 */ = function(_rL/* s3KE */){
  return E(_rL/* s3KE */)==100;
},
_rM/* ch1DataProduction23 */ = new T1(4,_rK/* FormStructure.Chapter1.ch1DataProduction24 */),
_rN/* ch1DataProduction22 */ = new T2(1,_rM/* FormStructure.Chapter1.ch1DataProduction23 */,_I/* GHC.Types.[] */),
_rO/* ch1DataProduction21 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_rN/* FormStructure.Chapter1.ch1DataProduction22 */),
_rP/* ch1DataProduction26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-sum"));
}),
_rQ/* ch1DataProduction25 */ = new T1(1,_rP/* FormStructure.Chapter1.ch1DataProduction26 */),
_rR/* ch1DataProduction28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_rS/* ch1DataProduction27 */ = new T1(1,_rR/* FormStructure.Chapter1.ch1DataProduction28 */),
_rT/* ch1DataProduction20 */ = {_:0,a:_rS/* FormStructure.Chapter1.ch1DataProduction27 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_rQ/* FormStructure.Chapter1.ch1DataProduction25 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_rO/* FormStructure.Chapter1.ch1DataProduction21 */},
_rU/* ch1DataProduction17 */ = new T2(3,_rT/* FormStructure.Chapter1.ch1DataProduction20 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_rV/* ch1DataProduction16 */ = new T2(1,_rU/* FormStructure.Chapter1.ch1DataProduction17 */,_I/* GHC.Types.[] */),
_rW/* ch1DataProduction34 */ = function(_rX/* s3Ky */){
  var _rY/* s3Kz */ = E(_rX/* s3Ky */);
  return (_rY/* s3Kz */<0) ? false : _rY/* s3Kz */<=100;
},
_rZ/* ch1DataProduction33 */ = new T1(4,_rW/* FormStructure.Chapter1.ch1DataProduction34 */),
_s0/* ch1DataProduction32 */ = new T2(1,_rZ/* FormStructure.Chapter1.ch1DataProduction33 */,_I/* GHC.Types.[] */),
_s1/* ch1DataProduction38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-open"));
}),
_s2/* ch1DataProduction37 */ = new T2(1,_s1/* FormStructure.Chapter1.ch1DataProduction38 */,_I/* GHC.Types.[] */),
_s3/* ch1DataProduction39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-closed"));
}),
_s4/* ch1DataProduction36 */ = new T2(1,_s3/* FormStructure.Chapter1.ch1DataProduction39 */,_s2/* FormStructure.Chapter1.ch1DataProduction37 */),
_s5/* ch1DataProduction40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-inside"));
}),
_s6/* ch1DataProduction35 */ = new T2(1,_s5/* FormStructure.Chapter1.ch1DataProduction40 */,_s4/* FormStructure.Chapter1.ch1DataProduction36 */),
_s7/* ch1DataProduction_accSumRule */ = new T2(0,_s6/* FormStructure.Chapter1.ch1DataProduction35 */,_rP/* FormStructure.Chapter1.ch1DataProduction26 */),
_s8/* ch1DataProduction31 */ = new T2(1,_s7/* FormStructure.Chapter1.ch1DataProduction_accSumRule */,_s0/* FormStructure.Chapter1.ch1DataProduction32 */),
_s9/* ch1DataProduction42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_sa/* ch1DataProduction41 */ = new T1(1,_s9/* FormStructure.Chapter1.ch1DataProduction42 */),
_sb/* ch1DataProduction45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_sc/* ch1DataProduction44 */ = new T2(1,_sb/* FormStructure.Chapter1.ch1DataProduction45 */,_I/* GHC.Types.[] */),
_sd/* ch1DataProduction46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_se/* ch1DataProduction43 */ = new T2(1,_sd/* FormStructure.Chapter1.ch1DataProduction46 */,_sc/* FormStructure.Chapter1.ch1DataProduction44 */),
_sf/* ch1DataProduction47 */ = new T1(1,_s1/* FormStructure.Chapter1.ch1DataProduction38 */),
_sg/* ch1DataProduction49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_sh/* ch1DataProduction48 */ = new T1(1,_sg/* FormStructure.Chapter1.ch1DataProduction49 */),
_si/* ch1DataProduction30 */ = {_:0,a:_sh/* FormStructure.Chapter1.ch1DataProduction48 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_sf/* FormStructure.Chapter1.ch1DataProduction47 */,d:_se/* FormStructure.Chapter1.ch1DataProduction43 */,e:_sa/* FormStructure.Chapter1.ch1DataProduction41 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_s8/* FormStructure.Chapter1.ch1DataProduction31 */},
_sj/* ch1DataProduction29 */ = new T2(3,_si/* FormStructure.Chapter1.ch1DataProduction30 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_sk/* ch1DataProduction15 */ = new T2(1,_sj/* FormStructure.Chapter1.ch1DataProduction29 */,_rV/* FormStructure.Chapter1.ch1DataProduction16 */),
_sl/* ch1DataProduction53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_sm/* ch1DataProduction52 */ = new T1(1,_sl/* FormStructure.Chapter1.ch1DataProduction53 */),
_sn/* ch1DataProduction56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_so/* ch1DataProduction55 */ = new T2(1,_sn/* FormStructure.Chapter1.ch1DataProduction56 */,_I/* GHC.Types.[] */),
_sp/* ch1DataProduction54 */ = new T2(1,_sd/* FormStructure.Chapter1.ch1DataProduction46 */,_so/* FormStructure.Chapter1.ch1DataProduction55 */),
_sq/* ch1DataProduction57 */ = new T1(1,_s3/* FormStructure.Chapter1.ch1DataProduction39 */),
_sr/* ch1DataProduction59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_ss/* ch1DataProduction58 */ = new T1(1,_sr/* FormStructure.Chapter1.ch1DataProduction59 */),
_st/* ch1DataProduction51 */ = {_:0,a:_ss/* FormStructure.Chapter1.ch1DataProduction58 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_sq/* FormStructure.Chapter1.ch1DataProduction57 */,d:_sp/* FormStructure.Chapter1.ch1DataProduction54 */,e:_sm/* FormStructure.Chapter1.ch1DataProduction52 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_s8/* FormStructure.Chapter1.ch1DataProduction31 */},
_su/* ch1DataProduction50 */ = new T2(3,_st/* FormStructure.Chapter1.ch1DataProduction51 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_sv/* ch1DataProduction14 */ = new T2(1,_su/* FormStructure.Chapter1.ch1DataProduction50 */,_sk/* FormStructure.Chapter1.ch1DataProduction15 */),
_sw/* ch1DataProduction63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_sx/* ch1DataProduction62 */ = new T2(1,_sw/* FormStructure.Chapter1.ch1DataProduction63 */,_I/* GHC.Types.[] */),
_sy/* ch1DataProduction64 */ = new T1(1,_s5/* FormStructure.Chapter1.ch1DataProduction40 */),
_sz/* ch1DataProduction66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_sA/* ch1DataProduction65 */ = new T1(1,_sz/* FormStructure.Chapter1.ch1DataProduction66 */),
_sB/* ch1DataProduction61 */ = {_:0,a:_sA/* FormStructure.Chapter1.ch1DataProduction65 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_sy/* FormStructure.Chapter1.ch1DataProduction64 */,d:_sx/* FormStructure.Chapter1.ch1DataProduction62 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_s8/* FormStructure.Chapter1.ch1DataProduction31 */},
_sC/* ch1DataProduction60 */ = new T2(3,_sB/* FormStructure.Chapter1.ch1DataProduction61 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_sD/* ch1DataProduction13 */ = new T2(1,_sC/* FormStructure.Chapter1.ch1DataProduction60 */,_sv/* FormStructure.Chapter1.ch1DataProduction14 */),
_sE/* ch1DataProduction70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_sF/* ch1DataProduction69 */ = new T1(1,_sE/* FormStructure.Chapter1.ch1DataProduction70 */),
_sG/* ch1DataProduction68 */ = {_:0,a:_sF/* FormStructure.Chapter1.ch1DataProduction69 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_sH/* ch1DataProduction12 */ = new T3(8,_sG/* FormStructure.Chapter1.ch1DataProduction68 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_sD/* FormStructure.Chapter1.ch1DataProduction13 */),
_sI/* ch1DataProduction10 */ = new T2(1,_sH/* FormStructure.Chapter1.ch1DataProduction12 */,_rH/* FormStructure.Chapter1.ch1DataProduction11 */),
_sJ/* ch1DataProduction112 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Skip if you do not want to share"));
}),
_sK/* ch1DataProduction111 */ = new T1(1,_sJ/* FormStructure.Chapter1.ch1DataProduction112 */),
_sL/* ch1DataProduction114 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_sM/* ch1DataProduction113 */ = new T1(1,_sL/* FormStructure.Chapter1.ch1DataProduction114 */),
_sN/* ch1DataProduction110 */ = {_:0,a:_sM/* FormStructure.Chapter1.ch1DataProduction113 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_sK/* FormStructure.Chapter1.ch1DataProduction111 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_sO/* ch1DataProduction91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-institutional"));
}),
_sP/* ch1DataProduction107 */ = new T1(1,_sO/* FormStructure.Chapter1.ch1DataProduction91 */),
_sQ/* ch1DataProduction109 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_sR/* ch1DataProduction108 */ = new T1(1,_sQ/* FormStructure.Chapter1.ch1DataProduction109 */),
_sS/* ch1DataProduction80 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-sum"));
}),
_sT/* ch1DataProduction88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-worldwide"));
}),
_sU/* ch1DataProduction87 */ = new T2(1,_sT/* FormStructure.Chapter1.ch1DataProduction88 */,_I/* GHC.Types.[] */),
_sV/* ch1DataProduction89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-european"));
}),
_sW/* ch1DataProduction86 */ = new T2(1,_sV/* FormStructure.Chapter1.ch1DataProduction89 */,_sU/* FormStructure.Chapter1.ch1DataProduction87 */),
_sX/* ch1DataProduction90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-national"));
}),
_sY/* ch1DataProduction85 */ = new T2(1,_sX/* FormStructure.Chapter1.ch1DataProduction90 */,_sW/* FormStructure.Chapter1.ch1DataProduction86 */),
_sZ/* ch1DataProduction84 */ = new T2(1,_sO/* FormStructure.Chapter1.ch1DataProduction91 */,_sY/* FormStructure.Chapter1.ch1DataProduction85 */),
_t0/* ch1DataProduction_fundingSumRule */ = new T2(0,_sZ/* FormStructure.Chapter1.ch1DataProduction84 */,_sS/* FormStructure.Chapter1.ch1DataProduction80 */),
_t1/* ch1DataProduction83 */ = new T2(1,_t0/* FormStructure.Chapter1.ch1DataProduction_fundingSumRule */,_s0/* FormStructure.Chapter1.ch1DataProduction32 */),
_t2/* ch1DataProduction106 */ = {_:0,a:_sR/* FormStructure.Chapter1.ch1DataProduction108 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_sP/* FormStructure.Chapter1.ch1DataProduction107 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_t1/* FormStructure.Chapter1.ch1DataProduction83 */},
_t3/* ch1DataProduction105 */ = new T2(3,_t2/* FormStructure.Chapter1.ch1DataProduction106 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_t4/* ch1DataProduction102 */ = new T1(1,_sX/* FormStructure.Chapter1.ch1DataProduction90 */),
_t5/* ch1DataProduction104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_t6/* ch1DataProduction103 */ = new T1(1,_t5/* FormStructure.Chapter1.ch1DataProduction104 */),
_t7/* ch1DataProduction101 */ = {_:0,a:_t6/* FormStructure.Chapter1.ch1DataProduction103 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_t4/* FormStructure.Chapter1.ch1DataProduction102 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_t1/* FormStructure.Chapter1.ch1DataProduction83 */},
_t8/* ch1DataProduction100 */ = new T2(3,_t7/* FormStructure.Chapter1.ch1DataProduction101 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_t9/* ch1DataProduction79 */ = new T1(1,_sS/* FormStructure.Chapter1.ch1DataProduction80 */),
_ta/* ch1DataProduction78 */ = {_:0,a:_rS/* FormStructure.Chapter1.ch1DataProduction27 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_t9/* FormStructure.Chapter1.ch1DataProduction79 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_rO/* FormStructure.Chapter1.ch1DataProduction21 */},
_tb/* ch1DataProduction77 */ = new T2(3,_ta/* FormStructure.Chapter1.ch1DataProduction78 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_tc/* ch1DataProduction76 */ = new T2(1,_tb/* FormStructure.Chapter1.ch1DataProduction77 */,_I/* GHC.Types.[] */),
_td/* ch1DataProduction92 */ = new T1(1,_sT/* FormStructure.Chapter1.ch1DataProduction88 */),
_te/* ch1DataProduction94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_tf/* ch1DataProduction93 */ = new T1(1,_te/* FormStructure.Chapter1.ch1DataProduction94 */),
_tg/* ch1DataProduction82 */ = {_:0,a:_tf/* FormStructure.Chapter1.ch1DataProduction93 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_td/* FormStructure.Chapter1.ch1DataProduction92 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_t1/* FormStructure.Chapter1.ch1DataProduction83 */},
_th/* ch1DataProduction81 */ = new T2(3,_tg/* FormStructure.Chapter1.ch1DataProduction82 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_ti/* ch1DataProduction75 */ = new T2(1,_th/* FormStructure.Chapter1.ch1DataProduction81 */,_tc/* FormStructure.Chapter1.ch1DataProduction76 */),
_tj/* ch1DataProduction97 */ = new T1(1,_sV/* FormStructure.Chapter1.ch1DataProduction89 */),
_tk/* ch1DataProduction99 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_tl/* ch1DataProduction98 */ = new T1(1,_tk/* FormStructure.Chapter1.ch1DataProduction99 */),
_tm/* ch1DataProduction96 */ = {_:0,a:_tl/* FormStructure.Chapter1.ch1DataProduction98 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_tj/* FormStructure.Chapter1.ch1DataProduction97 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_t1/* FormStructure.Chapter1.ch1DataProduction83 */},
_tn/* ch1DataProduction95 */ = new T2(3,_tm/* FormStructure.Chapter1.ch1DataProduction96 */,_rJ/* FormStructure.Chapter1.ch1DataProduction18 */),
_to/* ch1DataProduction74 */ = new T2(1,_tn/* FormStructure.Chapter1.ch1DataProduction95 */,_ti/* FormStructure.Chapter1.ch1DataProduction75 */),
_tp/* ch1DataProduction73 */ = new T2(1,_t8/* FormStructure.Chapter1.ch1DataProduction100 */,_to/* FormStructure.Chapter1.ch1DataProduction74 */),
_tq/* ch1DataProduction72 */ = new T2(1,_t3/* FormStructure.Chapter1.ch1DataProduction105 */,_tp/* FormStructure.Chapter1.ch1DataProduction73 */),
_tr/* ch1DataProduction71 */ = new T3(8,_sN/* FormStructure.Chapter1.ch1DataProduction110 */,_r8/* FormStructure.Chapter1.ch1DataProduction67 */,_tq/* FormStructure.Chapter1.ch1DataProduction72 */),
_ts/* ch1DataProduction9 */ = new T2(1,_tr/* FormStructure.Chapter1.ch1DataProduction71 */,_sI/* FormStructure.Chapter1.ch1DataProduction10 */),
_tt/* ch1DataProduction8 */ = new T2(1,_rG/* FormStructure.Chapter1.ch1DataProduction115 */,_ts/* FormStructure.Chapter1.ch1DataProduction9 */),
_tu/* ch1DataProduction7 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_pG/* FormStructure.Chapter1.ch1DataProduction223 */,_tt/* FormStructure.Chapter1.ch1DataProduction8 */),
_tv/* ch1DataProduction3 */ = new T2(1,_tu/* FormStructure.Chapter1.ch1DataProduction7 */,_pF/* FormStructure.Chapter1.ch1DataProduction4 */),
_tw/* ch1DataProduction2 */ = new T2(5,_pC/* FormStructure.Chapter1.ch1DataProduction224 */,_tv/* FormStructure.Chapter1.ch1DataProduction3 */),
_tx/* ch1DataProduction1 */ = new T2(1,_tw/* FormStructure.Chapter1.ch1DataProduction2 */,_I/* GHC.Types.[] */),
_ty/* ch1DataProduction229 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1.Production "));
}),
_tz/* ch1DataProduction228 */ = new T1(1,_ty/* FormStructure.Chapter1.ch1DataProduction229 */),
_tA/* ch1DataProduction227 */ = {_:0,a:_tz/* FormStructure.Chapter1.ch1DataProduction228 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tB/* ch1DataProduction */ = new T2(7,_tA/* FormStructure.Chapter1.ch1DataProduction227 */,_tx/* FormStructure.Chapter1.ch1DataProduction1 */),
_tC/* ch2DataProcessing256 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you process raw data, i.e. you produce secondary data?"));
}),
_tD/* ch2DataProcessing255 */ = new T1(1,_tC/* FormStructure.Chapter2.ch2DataProcessing256 */),
_tE/* ch2DataProcessing254 */ = {_:0,a:_tD/* FormStructure.Chapter2.ch2DataProcessing255 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_tF/* ch2DataProcessing6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_tG/* ch2DataProcessing5 */ = new T1(0,_tF/* FormStructure.Chapter2.ch2DataProcessing6 */),
_tH/* ch2DataProcessing4 */ = new T2(1,_tG/* FormStructure.Chapter2.ch2DataProcessing5 */,_I/* GHC.Types.[] */),
_tI/* ch2DataProcessing153 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_tJ/* ch2DataProcessing152 */ = new T1(0,_tI/* FormStructure.Chapter2.ch2DataProcessing153 */),
_tK/* ch2DataProcessing156 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_tL/* ch2DataProcessing155 */ = new T1(1,_tK/* FormStructure.Chapter2.ch2DataProcessing156 */),
_tM/* ch2DataProcessing154 */ = {_:0,a:_tL/* FormStructure.Chapter2.ch2DataProcessing155 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tN/* ch2DataProcessing151 */ = new T2(3,_tM/* FormStructure.Chapter2.ch2DataProcessing154 */,_tJ/* FormStructure.Chapter2.ch2DataProcessing152 */),
_tO/* ch2DataProcessing150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_tP/* ch2DataProcessing149 */ = new T1(1,_tO/* FormStructure.Chapter2.ch2DataProcessing150 */),
_tQ/* ch2DataProcessing148 */ = {_:0,a:_tP/* FormStructure.Chapter2.ch2DataProcessing149 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_tR/* ch2DataProcessing21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_tS/* ch2DataProcessing20 */ = new T1(0,_tR/* FormStructure.Chapter2.ch2DataProcessing21 */),
_tT/* ch2DataProcessing208 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-sum"));
}),
_tU/* ch2DataProcessing207 */ = new T1(1,_tT/* FormStructure.Chapter2.ch2DataProcessing208 */),
_tV/* ch2DataProcessing26 */ = function(_tW/* s4LL */){
  return E(_tW/* s4LL */)==100;
},
_tX/* ch2DataProcessing25 */ = new T1(4,_tV/* FormStructure.Chapter2.ch2DataProcessing26 */),
_tY/* ch2DataProcessing24 */ = new T2(1,_tX/* FormStructure.Chapter2.ch2DataProcessing25 */,_I/* GHC.Types.[] */),
_tZ/* ch2DataProcessing23 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_tY/* FormStructure.Chapter2.ch2DataProcessing24 */),
_u0/* ch2DataProcessing30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_u1/* ch2DataProcessing29 */ = new T1(1,_u0/* FormStructure.Chapter2.ch2DataProcessing30 */),
_u2/* ch2DataProcessing206 */ = {_:0,a:_u1/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_tU/* FormStructure.Chapter2.ch2DataProcessing207 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_tZ/* FormStructure.Chapter2.ch2DataProcessing23 */},
_u3/* ch2DataProcessing205 */ = new T2(3,_u2/* FormStructure.Chapter2.ch2DataProcessing206 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_u4/* ch2DataProcessing204 */ = new T2(1,_u3/* FormStructure.Chapter2.ch2DataProcessing205 */,_I/* GHC.Types.[] */),
_u5/* ch2DataProcessing132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_u6/* ch2DataProcessing131 */ = new T1(1,_u5/* FormStructure.Chapter2.ch2DataProcessing132 */),
_u7/* ch2DataProcessing36 */ = function(_u8/* s4LF */){
  var _u9/* s4LG */ = E(_u8/* s4LF */);
  return (_u9/* s4LG */<0) ? false : _u9/* s4LG */<=100;
},
_ua/* ch2DataProcessing35 */ = new T1(4,_u7/* FormStructure.Chapter2.ch2DataProcessing36 */),
_ub/* ch2DataProcessing34 */ = new T2(1,_ua/* FormStructure.Chapter2.ch2DataProcessing35 */,_I/* GHC.Types.[] */),
_uc/* ch2DataProcessing216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-worldwide"));
}),
_ud/* ch2DataProcessing215 */ = new T2(1,_uc/* FormStructure.Chapter2.ch2DataProcessing216 */,_I/* GHC.Types.[] */),
_ue/* ch2DataProcessing217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-european"));
}),
_uf/* ch2DataProcessing214 */ = new T2(1,_ue/* FormStructure.Chapter2.ch2DataProcessing217 */,_ud/* FormStructure.Chapter2.ch2DataProcessing215 */),
_ug/* ch2DataProcessing218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-national"));
}),
_uh/* ch2DataProcessing213 */ = new T2(1,_ug/* FormStructure.Chapter2.ch2DataProcessing218 */,_uf/* FormStructure.Chapter2.ch2DataProcessing214 */),
_ui/* ch2DataProcessing219 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-institutional"));
}),
_uj/* ch2DataProcessing212 */ = new T2(1,_ui/* FormStructure.Chapter2.ch2DataProcessing219 */,_uh/* FormStructure.Chapter2.ch2DataProcessing213 */),
_uk/* ch2DataProcessing_fundingSumRule1 */ = new T2(0,_uj/* FormStructure.Chapter2.ch2DataProcessing212 */,_tT/* FormStructure.Chapter2.ch2DataProcessing208 */),
_ul/* ch2DataProcessing211 */ = new T2(1,_uk/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule1 */,_ub/* FormStructure.Chapter2.ch2DataProcessing34 */),
_um/* ch2DataProcessing220 */ = new T1(1,_uc/* FormStructure.Chapter2.ch2DataProcessing216 */),
_un/* ch2DataProcessing210 */ = {_:0,a:_u6/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_um/* FormStructure.Chapter2.ch2DataProcessing220 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_ul/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uo/* ch2DataProcessing209 */ = new T2(3,_un/* FormStructure.Chapter2.ch2DataProcessing210 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_up/* ch2DataProcessing203 */ = new T2(1,_uo/* FormStructure.Chapter2.ch2DataProcessing209 */,_u4/* FormStructure.Chapter2.ch2DataProcessing204 */),
_uq/* ch2DataProcessing137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_ur/* ch2DataProcessing136 */ = new T1(1,_uq/* FormStructure.Chapter2.ch2DataProcessing137 */),
_us/* ch2DataProcessing223 */ = new T1(1,_ue/* FormStructure.Chapter2.ch2DataProcessing217 */),
_ut/* ch2DataProcessing222 */ = {_:0,a:_ur/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_us/* FormStructure.Chapter2.ch2DataProcessing223 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_ul/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uu/* ch2DataProcessing221 */ = new T2(3,_ut/* FormStructure.Chapter2.ch2DataProcessing222 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uv/* ch2DataProcessing202 */ = new T2(1,_uu/* FormStructure.Chapter2.ch2DataProcessing221 */,_up/* FormStructure.Chapter2.ch2DataProcessing203 */),
_uw/* ch2DataProcessing142 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_ux/* ch2DataProcessing141 */ = new T1(1,_uw/* FormStructure.Chapter2.ch2DataProcessing142 */),
_uy/* ch2DataProcessing226 */ = new T1(1,_ug/* FormStructure.Chapter2.ch2DataProcessing218 */),
_uz/* ch2DataProcessing225 */ = {_:0,a:_ux/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_uy/* FormStructure.Chapter2.ch2DataProcessing226 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_ul/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uA/* ch2DataProcessing224 */ = new T2(3,_uz/* FormStructure.Chapter2.ch2DataProcessing225 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uB/* ch2DataProcessing201 */ = new T2(1,_uA/* FormStructure.Chapter2.ch2DataProcessing224 */,_uv/* FormStructure.Chapter2.ch2DataProcessing202 */),
_uC/* ch2DataProcessing147 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_uD/* ch2DataProcessing146 */ = new T1(1,_uC/* FormStructure.Chapter2.ch2DataProcessing147 */),
_uE/* ch2DataProcessing229 */ = new T1(1,_ui/* FormStructure.Chapter2.ch2DataProcessing219 */),
_uF/* ch2DataProcessing228 */ = {_:0,a:_uD/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_uE/* FormStructure.Chapter2.ch2DataProcessing229 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_ul/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uG/* ch2DataProcessing227 */ = new T2(3,_uF/* FormStructure.Chapter2.ch2DataProcessing228 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uH/* ch2DataProcessing200 */ = new T2(1,_uG/* FormStructure.Chapter2.ch2DataProcessing227 */,_uB/* FormStructure.Chapter2.ch2DataProcessing201 */),
_uI/* ch2DataProcessing69 */ = 0,
_uJ/* ch2DataProcessing199 */ = new T3(8,_tQ/* FormStructure.Chapter2.ch2DataProcessing148 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_uH/* FormStructure.Chapter2.ch2DataProcessing200 */),
_uK/* ch2DataProcessing198 */ = new T2(1,_uJ/* FormStructure.Chapter2.ch2DataProcessing199 */,_I/* GHC.Types.[] */),
_uL/* ch2DataProcessing197 */ = new T2(1,_tN/* FormStructure.Chapter2.ch2DataProcessing151 */,_uK/* FormStructure.Chapter2.ch2DataProcessing198 */),
_uM/* ch2DataProcessing232 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_uN/* ch2DataProcessing231 */ = new T1(1,_uM/* FormStructure.Chapter2.ch2DataProcessing232 */),
_uO/* ch2DataProcessing230 */ = {_:0,a:_uN/* FormStructure.Chapter2.ch2DataProcessing231 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_uP/* ch2DataProcessing196 */ = new T3(8,_uO/* FormStructure.Chapter2.ch2DataProcessing230 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_uL/* FormStructure.Chapter2.ch2DataProcessing197 */),
_uQ/* ch2DataProcessing195 */ = new T2(1,_uP/* FormStructure.Chapter2.ch2DataProcessing196 */,_I/* GHC.Types.[] */),
_uR/* ch2DataProcessing170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_uS/* ch2DataProcessing169 */ = new T2(1,_uR/* FormStructure.Chapter2.ch2DataProcessing170 */,_I/* GHC.Types.[] */),
_uT/* ch2DataProcessing171 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_uU/* ch2DataProcessing168 */ = new T2(1,_uT/* FormStructure.Chapter2.ch2DataProcessing171 */,_uS/* FormStructure.Chapter2.ch2DataProcessing169 */),
_uV/* ch2DataProcessing172 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_uW/* ch2DataProcessing167 */ = new T2(1,_uV/* FormStructure.Chapter2.ch2DataProcessing172 */,_uU/* FormStructure.Chapter2.ch2DataProcessing168 */),
_uX/* ch2DataProcessing173 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_uY/* ch2DataProcessing166 */ = new T2(1,_uX/* FormStructure.Chapter2.ch2DataProcessing173 */,_uW/* FormStructure.Chapter2.ch2DataProcessing167 */),
_uZ/* ch2DataProcessing165 */ = new T1(1,_uY/* FormStructure.Chapter2.ch2DataProcessing166 */),
_v0/* ch2DataProcessing236 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_v1/* ch2DataProcessing235 */ = new T1(1,_v0/* FormStructure.Chapter2.ch2DataProcessing236 */),
_v2/* ch2DataProcessing238 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_2"));
}),
_v3/* ch2DataProcessing237 */ = new T2(1,_v2/* FormStructure.Chapter2.ch2DataProcessing238 */,_I/* GHC.Types.[] */),
_v4/* ch2DataProcessing240 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific raw data volume"));
}),
_v5/* ch2DataProcessing239 */ = new T1(1,_v4/* FormStructure.Chapter2.ch2DataProcessing240 */),
_v6/* ch2DataProcessing234 */ = {_:0,a:_v5/* FormStructure.Chapter2.ch2DataProcessing239 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_v3/* FormStructure.Chapter2.ch2DataProcessing237 */,e:_v1/* FormStructure.Chapter2.ch2DataProcessing235 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_v7/* ch2DataProcessing233 */ = new T2(3,_v6/* FormStructure.Chapter2.ch2DataProcessing234 */,_uZ/* FormStructure.Chapter2.ch2DataProcessing165 */),
_v8/* ch2DataProcessing194 */ = new T2(1,_v7/* FormStructure.Chapter2.ch2DataProcessing233 */,_uQ/* FormStructure.Chapter2.ch2DataProcessing195 */),
_v9/* ch2DataProcessing242 */ = new T1(0,_uT/* FormStructure.Chapter2.ch2DataProcessing171 */),
_va/* ch2DataProcessing244 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_vb/* ch2DataProcessing246 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_vc/* ch2DataProcessing245 */ = new T2(1,_vb/* FormStructure.Chapter2.ch2DataProcessing246 */,_I/* GHC.Types.[] */),
_vd/* ch2DataProcessing248 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_ve/* ch2DataProcessing247 */ = new T1(1,_vd/* FormStructure.Chapter2.ch2DataProcessing248 */),
_vf/* ch2DataProcessing250 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_vg/* ch2DataProcessing249 */ = new T1(1,_vf/* FormStructure.Chapter2.ch2DataProcessing250 */),
_vh/* ch2DataProcessing243 */ = {_:0,a:_vg/* FormStructure.Chapter2.ch2DataProcessing249 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_ve/* FormStructure.Chapter2.ch2DataProcessing247 */,d:_vc/* FormStructure.Chapter2.ch2DataProcessing245 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_va/* FormStructure.Chapter2.ch2DataProcessing244 */},
_vi/* ch2DataProcessing241 */ = new T2(3,_vh/* FormStructure.Chapter2.ch2DataProcessing243 */,_v9/* FormStructure.Chapter2.ch2DataProcessing242 */),
_vj/* ch2DataProcessing193 */ = new T2(1,_vi/* FormStructure.Chapter2.ch2DataProcessing241 */,_v8/* FormStructure.Chapter2.ch2DataProcessing194 */),
_vk/* ch2DataProcessing253 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_vl/* ch2DataProcessing252 */ = new T1(1,_vk/* FormStructure.Chapter2.ch2DataProcessing253 */),
_vm/* ch2DataProcessing251 */ = {_:0,a:_vl/* FormStructure.Chapter2.ch2DataProcessing252 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_vn/* ch2DataProcessing192 */ = new T3(8,_vm/* FormStructure.Chapter2.ch2DataProcessing251 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_vj/* FormStructure.Chapter2.ch2DataProcessing193 */),
_vo/* ch2DataProcessing118 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-sum"));
}),
_vp/* ch2DataProcessing117 */ = new T1(1,_vo/* FormStructure.Chapter2.ch2DataProcessing118 */),
_vq/* ch2DataProcessing116 */ = {_:0,a:_u1/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_vp/* FormStructure.Chapter2.ch2DataProcessing117 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_tZ/* FormStructure.Chapter2.ch2DataProcessing23 */},
_vr/* ch2DataProcessing115 */ = new T2(3,_vq/* FormStructure.Chapter2.ch2DataProcessing116 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vs/* ch2DataProcessing114 */ = new T2(1,_vr/* FormStructure.Chapter2.ch2DataProcessing115 */,_I/* GHC.Types.[] */),
_vt/* ch2DataProcessing126 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-worldwide"));
}),
_vu/* ch2DataProcessing125 */ = new T2(1,_vt/* FormStructure.Chapter2.ch2DataProcessing126 */,_I/* GHC.Types.[] */),
_vv/* ch2DataProcessing127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-european"));
}),
_vw/* ch2DataProcessing124 */ = new T2(1,_vv/* FormStructure.Chapter2.ch2DataProcessing127 */,_vu/* FormStructure.Chapter2.ch2DataProcessing125 */),
_vx/* ch2DataProcessing128 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-national"));
}),
_vy/* ch2DataProcessing123 */ = new T2(1,_vx/* FormStructure.Chapter2.ch2DataProcessing128 */,_vw/* FormStructure.Chapter2.ch2DataProcessing124 */),
_vz/* ch2DataProcessing129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-institutional"));
}),
_vA/* ch2DataProcessing122 */ = new T2(1,_vz/* FormStructure.Chapter2.ch2DataProcessing129 */,_vy/* FormStructure.Chapter2.ch2DataProcessing123 */),
_vB/* ch2DataProcessing_fundingSumRule */ = new T2(0,_vA/* FormStructure.Chapter2.ch2DataProcessing122 */,_vo/* FormStructure.Chapter2.ch2DataProcessing118 */),
_vC/* ch2DataProcessing121 */ = new T2(1,_vB/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule */,_ub/* FormStructure.Chapter2.ch2DataProcessing34 */),
_vD/* ch2DataProcessing130 */ = new T1(1,_vt/* FormStructure.Chapter2.ch2DataProcessing126 */),
_vE/* ch2DataProcessing120 */ = {_:0,a:_u6/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_vD/* FormStructure.Chapter2.ch2DataProcessing130 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_vC/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vF/* ch2DataProcessing119 */ = new T2(3,_vE/* FormStructure.Chapter2.ch2DataProcessing120 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vG/* ch2DataProcessing113 */ = new T2(1,_vF/* FormStructure.Chapter2.ch2DataProcessing119 */,_vs/* FormStructure.Chapter2.ch2DataProcessing114 */),
_vH/* ch2DataProcessing135 */ = new T1(1,_vv/* FormStructure.Chapter2.ch2DataProcessing127 */),
_vI/* ch2DataProcessing134 */ = {_:0,a:_ur/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_vH/* FormStructure.Chapter2.ch2DataProcessing135 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_vC/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vJ/* ch2DataProcessing133 */ = new T2(3,_vI/* FormStructure.Chapter2.ch2DataProcessing134 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vK/* ch2DataProcessing112 */ = new T2(1,_vJ/* FormStructure.Chapter2.ch2DataProcessing133 */,_vG/* FormStructure.Chapter2.ch2DataProcessing113 */),
_vL/* ch2DataProcessing140 */ = new T1(1,_vx/* FormStructure.Chapter2.ch2DataProcessing128 */),
_vM/* ch2DataProcessing139 */ = {_:0,a:_ux/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_vL/* FormStructure.Chapter2.ch2DataProcessing140 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_vC/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vN/* ch2DataProcessing138 */ = new T2(3,_vM/* FormStructure.Chapter2.ch2DataProcessing139 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vO/* ch2DataProcessing111 */ = new T2(1,_vN/* FormStructure.Chapter2.ch2DataProcessing138 */,_vK/* FormStructure.Chapter2.ch2DataProcessing112 */),
_vP/* ch2DataProcessing145 */ = new T1(1,_vz/* FormStructure.Chapter2.ch2DataProcessing129 */),
_vQ/* ch2DataProcessing144 */ = {_:0,a:_uD/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_vP/* FormStructure.Chapter2.ch2DataProcessing145 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_vC/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vR/* ch2DataProcessing143 */ = new T2(3,_vQ/* FormStructure.Chapter2.ch2DataProcessing144 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vS/* ch2DataProcessing110 */ = new T2(1,_vR/* FormStructure.Chapter2.ch2DataProcessing143 */,_vO/* FormStructure.Chapter2.ch2DataProcessing111 */),
_vT/* ch2DataProcessing109 */ = new T3(8,_tQ/* FormStructure.Chapter2.ch2DataProcessing148 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_vS/* FormStructure.Chapter2.ch2DataProcessing110 */),
_vU/* ch2DataProcessing108 */ = new T2(1,_vT/* FormStructure.Chapter2.ch2DataProcessing109 */,_I/* GHC.Types.[] */),
_vV/* ch2DataProcessing107 */ = new T2(1,_tN/* FormStructure.Chapter2.ch2DataProcessing151 */,_vU/* FormStructure.Chapter2.ch2DataProcessing108 */),
_vW/* ch2DataProcessing159 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_vX/* ch2DataProcessing158 */ = new T1(1,_vW/* FormStructure.Chapter2.ch2DataProcessing159 */),
_vY/* ch2DataProcessing161 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of data processing"));
}),
_vZ/* ch2DataProcessing160 */ = new T1(1,_vY/* FormStructure.Chapter2.ch2DataProcessing161 */),
_w0/* ch2DataProcessing157 */ = {_:0,a:_vZ/* FormStructure.Chapter2.ch2DataProcessing160 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_vX/* FormStructure.Chapter2.ch2DataProcessing158 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_w1/* ch2DataProcessing106 */ = new T3(8,_w0/* FormStructure.Chapter2.ch2DataProcessing157 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_vV/* FormStructure.Chapter2.ch2DataProcessing107 */),
_w2/* ch2DataProcessing13 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_w3/* ch2DataProcessing28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-sum"));
}),
_w4/* ch2DataProcessing27 */ = new T1(1,_w3/* FormStructure.Chapter2.ch2DataProcessing28 */),
_w5/* ch2DataProcessing22 */ = {_:0,a:_u1/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_w4/* FormStructure.Chapter2.ch2DataProcessing27 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_tZ/* FormStructure.Chapter2.ch2DataProcessing23 */},
_w6/* ch2DataProcessing19 */ = new T2(3,_w5/* FormStructure.Chapter2.ch2DataProcessing22 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_w7/* ch2DataProcessing18 */ = new T2(1,_w6/* FormStructure.Chapter2.ch2DataProcessing19 */,_I/* GHC.Types.[] */),
_w8/* ch2DataProcessing40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-open"));
}),
_w9/* ch2DataProcessing39 */ = new T2(1,_w8/* FormStructure.Chapter2.ch2DataProcessing40 */,_I/* GHC.Types.[] */),
_wa/* ch2DataProcessing41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-closed"));
}),
_wb/* ch2DataProcessing38 */ = new T2(1,_wa/* FormStructure.Chapter2.ch2DataProcessing41 */,_w9/* FormStructure.Chapter2.ch2DataProcessing39 */),
_wc/* ch2DataProcessing42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-inside"));
}),
_wd/* ch2DataProcessing37 */ = new T2(1,_wc/* FormStructure.Chapter2.ch2DataProcessing42 */,_wb/* FormStructure.Chapter2.ch2DataProcessing38 */),
_we/* ch2DataProcessing_accSumRule */ = new T2(0,_wd/* FormStructure.Chapter2.ch2DataProcessing37 */,_w3/* FormStructure.Chapter2.ch2DataProcessing28 */),
_wf/* ch2DataProcessing33 */ = new T2(1,_we/* FormStructure.Chapter2.ch2DataProcessing_accSumRule */,_ub/* FormStructure.Chapter2.ch2DataProcessing34 */),
_wg/* ch2DataProcessing44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_wh/* ch2DataProcessing43 */ = new T1(1,_wg/* FormStructure.Chapter2.ch2DataProcessing44 */),
_wi/* ch2DataProcessing47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_wj/* ch2DataProcessing46 */ = new T2(1,_wi/* FormStructure.Chapter2.ch2DataProcessing47 */,_I/* GHC.Types.[] */),
_wk/* ch2DataProcessing48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_wl/* ch2DataProcessing45 */ = new T2(1,_wk/* FormStructure.Chapter2.ch2DataProcessing48 */,_wj/* FormStructure.Chapter2.ch2DataProcessing46 */),
_wm/* ch2DataProcessing49 */ = new T1(1,_w8/* FormStructure.Chapter2.ch2DataProcessing40 */),
_wn/* ch2DataProcessing51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_wo/* ch2DataProcessing50 */ = new T1(1,_wn/* FormStructure.Chapter2.ch2DataProcessing51 */),
_wp/* ch2DataProcessing32 */ = {_:0,a:_wo/* FormStructure.Chapter2.ch2DataProcessing50 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_wm/* FormStructure.Chapter2.ch2DataProcessing49 */,d:_wl/* FormStructure.Chapter2.ch2DataProcessing45 */,e:_wh/* FormStructure.Chapter2.ch2DataProcessing43 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_wf/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wq/* ch2DataProcessing31 */ = new T2(3,_wp/* FormStructure.Chapter2.ch2DataProcessing32 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wr/* ch2DataProcessing17 */ = new T2(1,_wq/* FormStructure.Chapter2.ch2DataProcessing31 */,_w7/* FormStructure.Chapter2.ch2DataProcessing18 */),
_ws/* ch2DataProcessing55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_wt/* ch2DataProcessing54 */ = new T1(1,_ws/* FormStructure.Chapter2.ch2DataProcessing55 */),
_wu/* ch2DataProcessing58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_wv/* ch2DataProcessing57 */ = new T2(1,_wu/* FormStructure.Chapter2.ch2DataProcessing58 */,_I/* GHC.Types.[] */),
_ww/* ch2DataProcessing56 */ = new T2(1,_wk/* FormStructure.Chapter2.ch2DataProcessing48 */,_wv/* FormStructure.Chapter2.ch2DataProcessing57 */),
_wx/* ch2DataProcessing59 */ = new T1(1,_wa/* FormStructure.Chapter2.ch2DataProcessing41 */),
_wy/* ch2DataProcessing61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_wz/* ch2DataProcessing60 */ = new T1(1,_wy/* FormStructure.Chapter2.ch2DataProcessing61 */),
_wA/* ch2DataProcessing53 */ = {_:0,a:_wz/* FormStructure.Chapter2.ch2DataProcessing60 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_wx/* FormStructure.Chapter2.ch2DataProcessing59 */,d:_ww/* FormStructure.Chapter2.ch2DataProcessing56 */,e:_wt/* FormStructure.Chapter2.ch2DataProcessing54 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_wf/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wB/* ch2DataProcessing52 */ = new T2(3,_wA/* FormStructure.Chapter2.ch2DataProcessing53 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wC/* ch2DataProcessing16 */ = new T2(1,_wB/* FormStructure.Chapter2.ch2DataProcessing52 */,_wr/* FormStructure.Chapter2.ch2DataProcessing17 */),
_wD/* ch2DataProcessing65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_wE/* ch2DataProcessing64 */ = new T2(1,_wD/* FormStructure.Chapter2.ch2DataProcessing65 */,_I/* GHC.Types.[] */),
_wF/* ch2DataProcessing66 */ = new T1(1,_wc/* FormStructure.Chapter2.ch2DataProcessing42 */),
_wG/* ch2DataProcessing68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_wH/* ch2DataProcessing67 */ = new T1(1,_wG/* FormStructure.Chapter2.ch2DataProcessing68 */),
_wI/* ch2DataProcessing63 */ = {_:0,a:_wH/* FormStructure.Chapter2.ch2DataProcessing67 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_wF/* FormStructure.Chapter2.ch2DataProcessing66 */,d:_wE/* FormStructure.Chapter2.ch2DataProcessing64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_wf/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wJ/* ch2DataProcessing62 */ = new T2(3,_wI/* FormStructure.Chapter2.ch2DataProcessing63 */,_tS/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wK/* ch2DataProcessing15 */ = new T2(1,_wJ/* FormStructure.Chapter2.ch2DataProcessing62 */,_wC/* FormStructure.Chapter2.ch2DataProcessing16 */),
_wL/* ch2DataProcessing72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_wM/* ch2DataProcessing71 */ = new T1(1,_wL/* FormStructure.Chapter2.ch2DataProcessing72 */),
_wN/* ch2DataProcessing70 */ = {_:0,a:_wM/* FormStructure.Chapter2.ch2DataProcessing71 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_wO/* ch2DataProcessing14 */ = new T3(8,_wN/* FormStructure.Chapter2.ch2DataProcessing70 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_wK/* FormStructure.Chapter2.ch2DataProcessing15 */),
_wP/* ch2DataProcessing12 */ = new T2(1,_wO/* FormStructure.Chapter2.ch2DataProcessing14 */,_w2/* FormStructure.Chapter2.ch2DataProcessing13 */),
_wQ/* ch2DataProcessing103 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_wR/* ch2DataProcessing102 */ = new T1(1,_wQ/* FormStructure.Chapter2.ch2DataProcessing103 */),
_wS/* ch2DataProcessing105 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_wT/* ch2DataProcessing104 */ = new T1(1,_wS/* FormStructure.Chapter2.ch2DataProcessing105 */),
_wU/* ch2DataProcessing101 */ = {_:0,a:_wT/* FormStructure.Chapter2.ch2DataProcessing104 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_wR/* FormStructure.Chapter2.ch2DataProcessing102 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_wV/* ch2DataProcessing82 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_wW/* ch2DataProcessing81 */ = new T1(0,_wV/* FormStructure.Chapter2.ch2DataProcessing82 */),
_wX/* ch2DataProcessing80 */ = new T2(1,_wW/* FormStructure.Chapter2.ch2DataProcessing81 */,_I/* GHC.Types.[] */),
_wY/* ch2DataProcessing84 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_wZ/* ch2DataProcessing83 */ = new T1(0,_wY/* FormStructure.Chapter2.ch2DataProcessing84 */),
_x0/* ch2DataProcessing79 */ = new T2(1,_wZ/* FormStructure.Chapter2.ch2DataProcessing83 */,_wX/* FormStructure.Chapter2.ch2DataProcessing80 */),
_x1/* ch2DataProcessing86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_x2/* ch2DataProcessing85 */ = new T1(0,_x1/* FormStructure.Chapter2.ch2DataProcessing86 */),
_x3/* ch2DataProcessing78 */ = new T2(1,_x2/* FormStructure.Chapter2.ch2DataProcessing85 */,_x0/* FormStructure.Chapter2.ch2DataProcessing79 */),
_x4/* ch2DataProcessing88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_x5/* ch2DataProcessing87 */ = new T1(0,_x4/* FormStructure.Chapter2.ch2DataProcessing88 */),
_x6/* ch2DataProcessing77 */ = new T2(1,_x5/* FormStructure.Chapter2.ch2DataProcessing87 */,_x3/* FormStructure.Chapter2.ch2DataProcessing78 */),
_x7/* ch2DataProcessing91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_x8/* ch2DataProcessing90 */ = new T1(1,_x7/* FormStructure.Chapter2.ch2DataProcessing91 */),
_x9/* ch2DataProcessing93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_xa/* ch2DataProcessing92 */ = new T1(1,_x9/* FormStructure.Chapter2.ch2DataProcessing93 */),
_xb/* ch2DataProcessing89 */ = {_:0,a:_xa/* FormStructure.Chapter2.ch2DataProcessing92 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_x8/* FormStructure.Chapter2.ch2DataProcessing90 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xc/* ch2DataProcessing76 */ = new T2(5,_xb/* FormStructure.Chapter2.ch2DataProcessing89 */,_x6/* FormStructure.Chapter2.ch2DataProcessing77 */),
_xd/* ch2DataProcessing75 */ = new T2(1,_xc/* FormStructure.Chapter2.ch2DataProcessing76 */,_I/* GHC.Types.[] */),
_xe/* ch2DataProcessing97 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_xf/* ch2DataProcessing96 */ = new T1(0,_xe/* FormStructure.Chapter2.ch2DataProcessing97 */),
_xg/* ch2DataProcessing95 */ = new T2(1,_xf/* FormStructure.Chapter2.ch2DataProcessing96 */,_tH/* FormStructure.Chapter2.ch2DataProcessing4 */),
_xh/* ch2DataProcessing100 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_xi/* ch2DataProcessing99 */ = new T1(1,_xh/* FormStructure.Chapter2.ch2DataProcessing100 */),
_xj/* ch2DataProcessing98 */ = {_:0,a:_xi/* FormStructure.Chapter2.ch2DataProcessing99 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xk/* ch2DataProcessing94 */ = new T2(5,_xj/* FormStructure.Chapter2.ch2DataProcessing98 */,_xg/* FormStructure.Chapter2.ch2DataProcessing95 */),
_xl/* ch2DataProcessing74 */ = new T2(1,_xk/* FormStructure.Chapter2.ch2DataProcessing94 */,_xd/* FormStructure.Chapter2.ch2DataProcessing75 */),
_xm/* ch2DataProcessing73 */ = new T3(8,_wU/* FormStructure.Chapter2.ch2DataProcessing101 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_xl/* FormStructure.Chapter2.ch2DataProcessing74 */),
_xn/* ch2DataProcessing11 */ = new T2(1,_xm/* FormStructure.Chapter2.ch2DataProcessing73 */,_wP/* FormStructure.Chapter2.ch2DataProcessing12 */),
_xo/* ch2DataProcessing10 */ = new T2(1,_w1/* FormStructure.Chapter2.ch2DataProcessing106 */,_xn/* FormStructure.Chapter2.ch2DataProcessing11 */),
_xp/* ch2DataProcessing176 */ = new T2(1,_q5/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_xq/* ch2DataProcessing178 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_xr/* ch2DataProcessing179 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_xs/* ch2DataProcessing177 */ = new T2(2,_xr/* FormStructure.Chapter2.ch2DataProcessing179 */,_xq/* FormStructure.Chapter2.ch2DataProcessing178 */),
_xt/* ch2DataProcessing175 */ = new T2(1,_xs/* FormStructure.Chapter2.ch2DataProcessing177 */,_xp/* FormStructure.Chapter2.ch2DataProcessing176 */),
_xu/* ch2DataProcessing181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_xv/* ch2DataProcessing180 */ = new T1(1,_xu/* FormStructure.Chapter2.ch2DataProcessing181 */),
_xw/* ch2DataProcessing184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_xx/* ch2DataProcessing183 */ = new T2(1,_xw/* FormStructure.Chapter2.ch2DataProcessing184 */,_I/* GHC.Types.[] */),
_xy/* ch2DataProcessing185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_xz/* ch2DataProcessing182 */ = new T2(1,_xy/* FormStructure.Chapter2.ch2DataProcessing185 */,_xx/* FormStructure.Chapter2.ch2DataProcessing183 */),
_xA/* ch2DataProcessing186 */ = new T1(1,_xr/* FormStructure.Chapter2.ch2DataProcessing179 */),
_xB/* ch2DataProcessing188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_xC/* ch2DataProcessing187 */ = new T1(1,_xB/* FormStructure.Chapter2.ch2DataProcessing188 */),
_xD/* ch2DataProcessing174 */ = {_:0,a:_xC/* FormStructure.Chapter2.ch2DataProcessing187 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_xA/* FormStructure.Chapter2.ch2DataProcessing186 */,d:_xz/* FormStructure.Chapter2.ch2DataProcessing182 */,e:_xv/* FormStructure.Chapter2.ch2DataProcessing180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_xt/* FormStructure.Chapter2.ch2DataProcessing175 */},
_xE/* ch2DataProcessing164 */ = new T2(3,_xD/* FormStructure.Chapter2.ch2DataProcessing174 */,_uZ/* FormStructure.Chapter2.ch2DataProcessing165 */),
_xF/* ch2DataProcessing163 */ = new T2(1,_xE/* FormStructure.Chapter2.ch2DataProcessing164 */,_I/* GHC.Types.[] */),
_xG/* ch2DataProcessing191 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_xH/* ch2DataProcessing190 */ = new T1(1,_xG/* FormStructure.Chapter2.ch2DataProcessing191 */),
_xI/* ch2DataProcessing189 */ = {_:0,a:_xH/* FormStructure.Chapter2.ch2DataProcessing190 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xJ/* ch2DataProcessing162 */ = new T3(8,_xI/* FormStructure.Chapter2.ch2DataProcessing189 */,_uI/* FormStructure.Chapter2.ch2DataProcessing69 */,_xF/* FormStructure.Chapter2.ch2DataProcessing163 */),
_xK/* ch2DataProcessing9 */ = new T2(1,_xJ/* FormStructure.Chapter2.ch2DataProcessing162 */,_xo/* FormStructure.Chapter2.ch2DataProcessing10 */),
_xL/* ch2DataProcessing8 */ = new T2(1,_vn/* FormStructure.Chapter2.ch2DataProcessing192 */,_xK/* FormStructure.Chapter2.ch2DataProcessing9 */),
_xM/* ch2DataProcessing7 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_xe/* FormStructure.Chapter2.ch2DataProcessing97 */,_xL/* FormStructure.Chapter2.ch2DataProcessing8 */),
_xN/* ch2DataProcessing3 */ = new T2(1,_xM/* FormStructure.Chapter2.ch2DataProcessing7 */,_tH/* FormStructure.Chapter2.ch2DataProcessing4 */),
_xO/* ch2DataProcessing2 */ = new T2(5,_tE/* FormStructure.Chapter2.ch2DataProcessing254 */,_xN/* FormStructure.Chapter2.ch2DataProcessing3 */),
_xP/* ch2DataProcessing1 */ = new T2(1,_xO/* FormStructure.Chapter2.ch2DataProcessing2 */,_I/* GHC.Types.[] */),
_xQ/* ch2DataProcessing259 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("2.Processing "));
}),
_xR/* ch2DataProcessing258 */ = new T1(1,_xQ/* FormStructure.Chapter2.ch2DataProcessing259 */),
_xS/* ch2DataProcessing257 */ = {_:0,a:_xR/* FormStructure.Chapter2.ch2DataProcessing258 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_xT/* ch2DataProcessing */ = new T2(7,_xS/* FormStructure.Chapter2.ch2DataProcessing257 */,_xP/* FormStructure.Chapter2.ch2DataProcessing1 */),
_xU/* ch3DataUsage264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you use data, i.e. to perform analyses?"));
}),
_xV/* ch3DataUsage263 */ = new T1(1,_xU/* FormStructure.Chapter3.ch3DataUsage264 */),
_xW/* ch3DataUsage262 */ = {_:0,a:_xV/* FormStructure.Chapter3.ch3DataUsage263 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xX/* ch3DataUsage6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_xY/* ch3DataUsage5 */ = new T1(0,_xX/* FormStructure.Chapter3.ch3DataUsage6 */),
_xZ/* ch3DataUsage4 */ = new T2(1,_xY/* FormStructure.Chapter3.ch3DataUsage5 */,_I/* GHC.Types.[] */),
_y0/* ch3DataUsage258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("A typical usage is performing a certain analysis."));
}),
_y1/* ch3DataUsage257 */ = new T1(1,_y0/* FormStructure.Chapter3.ch3DataUsage258 */),
_y2/* ch3DataUsage260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Describe the usage"));
}),
_y3/* ch3DataUsage259 */ = new T1(1,_y2/* FormStructure.Chapter3.ch3DataUsage260 */),
_y4/* ch3DataUsage256 */ = {_:0,a:_y3/* FormStructure.Chapter3.ch3DataUsage259 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_y1/* FormStructure.Chapter3.ch3DataUsage257 */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_y5/* ch3DataUsage255 */ = new T1(1,_y4/* FormStructure.Chapter3.ch3DataUsage256 */),
_y6/* ch3DataUsage254 */ = new T2(1,_y5/* FormStructure.Chapter3.ch3DataUsage255 */,_I/* GHC.Types.[] */),
_y7/* ch3DataUsage261 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_y8/* ch3DataUsage70 */ = 0,
_y9/* ch3DataUsage253 */ = new T3(8,_y7/* FormStructure.Chapter3.ch3DataUsage261 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_y6/* FormStructure.Chapter3.ch3DataUsage254 */),
_ya/* ch3DataUsage119 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-sum"));
}),
_yb/* ch3DataUsage118 */ = new T1(1,_ya/* FormStructure.Chapter3.ch3DataUsage119 */),
_yc/* ch3DataUsage27 */ = function(_yd/* s5Q4 */){
  return E(_yd/* s5Q4 */)==100;
},
_ye/* ch3DataUsage26 */ = new T1(4,_yc/* FormStructure.Chapter3.ch3DataUsage27 */),
_yf/* ch3DataUsage25 */ = new T2(1,_ye/* FormStructure.Chapter3.ch3DataUsage26 */,_I/* GHC.Types.[] */),
_yg/* ch3DataUsage24 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_yf/* FormStructure.Chapter3.ch3DataUsage25 */),
_yh/* ch3DataUsage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_yi/* ch3DataUsage30 */ = new T1(1,_yh/* FormStructure.Chapter3.ch3DataUsage31 */),
_yj/* ch3DataUsage117 */ = {_:0,a:_yi/* FormStructure.Chapter3.ch3DataUsage30 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_yb/* FormStructure.Chapter3.ch3DataUsage118 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yg/* FormStructure.Chapter3.ch3DataUsage24 */},
_yk/* ch3DataUsage22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_yl/* ch3DataUsage21 */ = new T1(0,_yk/* FormStructure.Chapter3.ch3DataUsage22 */),
_ym/* ch3DataUsage116 */ = new T2(3,_yj/* FormStructure.Chapter3.ch3DataUsage117 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_yn/* ch3DataUsage115 */ = new T2(1,_ym/* FormStructure.Chapter3.ch3DataUsage116 */,_I/* GHC.Types.[] */),
_yo/* ch3DataUsage125 */ = function(_yp/* s5PY */){
  var _yq/* s5PZ */ = E(_yp/* s5PY */);
  return (_yq/* s5PZ */<0) ? false : _yq/* s5PZ */<=100;
},
_yr/* ch3DataUsage124 */ = new T1(4,_yo/* FormStructure.Chapter3.ch3DataUsage125 */),
_ys/* ch3DataUsage123 */ = new T2(1,_yr/* FormStructure.Chapter3.ch3DataUsage124 */,_I/* GHC.Types.[] */),
_yt/* ch3DataUsage130 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-worldwide"));
}),
_yu/* ch3DataUsage129 */ = new T2(1,_yt/* FormStructure.Chapter3.ch3DataUsage130 */,_I/* GHC.Types.[] */),
_yv/* ch3DataUsage131 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-european"));
}),
_yw/* ch3DataUsage128 */ = new T2(1,_yv/* FormStructure.Chapter3.ch3DataUsage131 */,_yu/* FormStructure.Chapter3.ch3DataUsage129 */),
_yx/* ch3DataUsage132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-national"));
}),
_yy/* ch3DataUsage127 */ = new T2(1,_yx/* FormStructure.Chapter3.ch3DataUsage132 */,_yw/* FormStructure.Chapter3.ch3DataUsage128 */),
_yz/* ch3DataUsage133 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-institutional"));
}),
_yA/* ch3DataUsage126 */ = new T2(1,_yz/* FormStructure.Chapter3.ch3DataUsage133 */,_yy/* FormStructure.Chapter3.ch3DataUsage127 */),
_yB/* ch3DataUsage_fundingSumRule */ = new T2(0,_yA/* FormStructure.Chapter3.ch3DataUsage126 */,_ya/* FormStructure.Chapter3.ch3DataUsage119 */),
_yC/* ch3DataUsage122 */ = new T2(1,_yB/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule */,_ys/* FormStructure.Chapter3.ch3DataUsage123 */),
_yD/* ch3DataUsage134 */ = new T1(1,_yt/* FormStructure.Chapter3.ch3DataUsage130 */),
_yE/* ch3DataUsage136 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_yF/* ch3DataUsage135 */ = new T1(1,_yE/* FormStructure.Chapter3.ch3DataUsage136 */),
_yG/* ch3DataUsage121 */ = {_:0,a:_yF/* FormStructure.Chapter3.ch3DataUsage135 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_yD/* FormStructure.Chapter3.ch3DataUsage134 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yC/* FormStructure.Chapter3.ch3DataUsage122 */},
_yH/* ch3DataUsage120 */ = new T2(3,_yG/* FormStructure.Chapter3.ch3DataUsage121 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_yI/* ch3DataUsage114 */ = new T2(1,_yH/* FormStructure.Chapter3.ch3DataUsage120 */,_yn/* FormStructure.Chapter3.ch3DataUsage115 */),
_yJ/* ch3DataUsage139 */ = new T1(1,_yv/* FormStructure.Chapter3.ch3DataUsage131 */),
_yK/* ch3DataUsage141 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_yL/* ch3DataUsage140 */ = new T1(1,_yK/* FormStructure.Chapter3.ch3DataUsage141 */),
_yM/* ch3DataUsage138 */ = {_:0,a:_yL/* FormStructure.Chapter3.ch3DataUsage140 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_yJ/* FormStructure.Chapter3.ch3DataUsage139 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yC/* FormStructure.Chapter3.ch3DataUsage122 */},
_yN/* ch3DataUsage137 */ = new T2(3,_yM/* FormStructure.Chapter3.ch3DataUsage138 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_yO/* ch3DataUsage113 */ = new T2(1,_yN/* FormStructure.Chapter3.ch3DataUsage137 */,_yI/* FormStructure.Chapter3.ch3DataUsage114 */),
_yP/* ch3DataUsage144 */ = new T1(1,_yx/* FormStructure.Chapter3.ch3DataUsage132 */),
_yQ/* ch3DataUsage146 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_yR/* ch3DataUsage145 */ = new T1(1,_yQ/* FormStructure.Chapter3.ch3DataUsage146 */),
_yS/* ch3DataUsage143 */ = {_:0,a:_yR/* FormStructure.Chapter3.ch3DataUsage145 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_yP/* FormStructure.Chapter3.ch3DataUsage144 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yC/* FormStructure.Chapter3.ch3DataUsage122 */},
_yT/* ch3DataUsage142 */ = new T2(3,_yS/* FormStructure.Chapter3.ch3DataUsage143 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_yU/* ch3DataUsage112 */ = new T2(1,_yT/* FormStructure.Chapter3.ch3DataUsage142 */,_yO/* FormStructure.Chapter3.ch3DataUsage113 */),
_yV/* ch3DataUsage149 */ = new T1(1,_yz/* FormStructure.Chapter3.ch3DataUsage133 */),
_yW/* ch3DataUsage151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_yX/* ch3DataUsage150 */ = new T1(1,_yW/* FormStructure.Chapter3.ch3DataUsage151 */),
_yY/* ch3DataUsage148 */ = {_:0,a:_yX/* FormStructure.Chapter3.ch3DataUsage150 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_yV/* FormStructure.Chapter3.ch3DataUsage149 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yC/* FormStructure.Chapter3.ch3DataUsage122 */},
_yZ/* ch3DataUsage147 */ = new T2(3,_yY/* FormStructure.Chapter3.ch3DataUsage148 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_z0/* ch3DataUsage111 */ = new T2(1,_yZ/* FormStructure.Chapter3.ch3DataUsage147 */,_yU/* FormStructure.Chapter3.ch3DataUsage112 */),
_z1/* ch3DataUsage154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_z2/* ch3DataUsage153 */ = new T1(1,_z1/* FormStructure.Chapter3.ch3DataUsage154 */),
_z3/* ch3DataUsage152 */ = {_:0,a:_z2/* FormStructure.Chapter3.ch3DataUsage153 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_z4/* ch3DataUsage110 */ = new T3(8,_z3/* FormStructure.Chapter3.ch3DataUsage152 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_z0/* FormStructure.Chapter3.ch3DataUsage111 */),
_z5/* ch3DataUsage109 */ = new T2(1,_z4/* FormStructure.Chapter3.ch3DataUsage110 */,_I/* GHC.Types.[] */),
_z6/* ch3DataUsage157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_z7/* ch3DataUsage156 */ = new T1(0,_z6/* FormStructure.Chapter3.ch3DataUsage157 */),
_z8/* ch3DataUsage160 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_z9/* ch3DataUsage159 */ = new T1(1,_z8/* FormStructure.Chapter3.ch3DataUsage160 */),
_za/* ch3DataUsage158 */ = {_:0,a:_z9/* FormStructure.Chapter3.ch3DataUsage159 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_zb/* ch3DataUsage155 */ = new T2(3,_za/* FormStructure.Chapter3.ch3DataUsage158 */,_z7/* FormStructure.Chapter3.ch3DataUsage156 */),
_zc/* ch3DataUsage108 */ = new T2(1,_zb/* FormStructure.Chapter3.ch3DataUsage155 */,_z5/* FormStructure.Chapter3.ch3DataUsage109 */),
_zd/* ch3DataUsage163 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_ze/* ch3DataUsage162 */ = new T1(1,_zd/* FormStructure.Chapter3.ch3DataUsage163 */),
_zf/* ch3DataUsage165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of secondary data production"));
}),
_zg/* ch3DataUsage164 */ = new T1(1,_zf/* FormStructure.Chapter3.ch3DataUsage165 */),
_zh/* ch3DataUsage161 */ = {_:0,a:_zg/* FormStructure.Chapter3.ch3DataUsage164 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_ze/* FormStructure.Chapter3.ch3DataUsage162 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_zi/* ch3DataUsage107 */ = new T3(8,_zh/* FormStructure.Chapter3.ch3DataUsage161 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_zc/* FormStructure.Chapter3.ch3DataUsage108 */),
_zj/* ch3DataUsage14 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_zk/* ch3DataUsage29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-sum"));
}),
_zl/* ch3DataUsage28 */ = new T1(1,_zk/* FormStructure.Chapter3.ch3DataUsage29 */),
_zm/* ch3DataUsage23 */ = {_:0,a:_yi/* FormStructure.Chapter3.ch3DataUsage30 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_zl/* FormStructure.Chapter3.ch3DataUsage28 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yg/* FormStructure.Chapter3.ch3DataUsage24 */},
_zn/* ch3DataUsage20 */ = new T2(3,_zm/* FormStructure.Chapter3.ch3DataUsage23 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_zo/* ch3DataUsage19 */ = new T2(1,_zn/* FormStructure.Chapter3.ch3DataUsage20 */,_I/* GHC.Types.[] */),
_zp/* ch3DataUsage37 */ = function(_zq/* s5Q8 */){
  return E(_zq/* s5Q8 */)<=100;
},
_zr/* ch3DataUsage36 */ = new T1(4,_zp/* FormStructure.Chapter3.ch3DataUsage37 */),
_zs/* ch3DataUsage35 */ = new T2(1,_zr/* FormStructure.Chapter3.ch3DataUsage36 */,_I/* GHC.Types.[] */),
_zt/* ch3DataUsage41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-open"));
}),
_zu/* ch3DataUsage40 */ = new T2(1,_zt/* FormStructure.Chapter3.ch3DataUsage41 */,_I/* GHC.Types.[] */),
_zv/* ch3DataUsage42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-closed"));
}),
_zw/* ch3DataUsage39 */ = new T2(1,_zv/* FormStructure.Chapter3.ch3DataUsage42 */,_zu/* FormStructure.Chapter3.ch3DataUsage40 */),
_zx/* ch3DataUsage43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-inside"));
}),
_zy/* ch3DataUsage38 */ = new T2(1,_zx/* FormStructure.Chapter3.ch3DataUsage43 */,_zw/* FormStructure.Chapter3.ch3DataUsage39 */),
_zz/* ch3DataUsage_accSumRule */ = new T2(0,_zy/* FormStructure.Chapter3.ch3DataUsage38 */,_zk/* FormStructure.Chapter3.ch3DataUsage29 */),
_zA/* ch3DataUsage34 */ = new T2(1,_zz/* FormStructure.Chapter3.ch3DataUsage_accSumRule */,_zs/* FormStructure.Chapter3.ch3DataUsage35 */),
_zB/* ch3DataUsage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_zC/* ch3DataUsage44 */ = new T1(1,_zB/* FormStructure.Chapter3.ch3DataUsage45 */),
_zD/* ch3DataUsage48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_zE/* ch3DataUsage47 */ = new T2(1,_zD/* FormStructure.Chapter3.ch3DataUsage48 */,_I/* GHC.Types.[] */),
_zF/* ch3DataUsage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_zG/* ch3DataUsage46 */ = new T2(1,_zF/* FormStructure.Chapter3.ch3DataUsage49 */,_zE/* FormStructure.Chapter3.ch3DataUsage47 */),
_zH/* ch3DataUsage50 */ = new T1(1,_zt/* FormStructure.Chapter3.ch3DataUsage41 */),
_zI/* ch3DataUsage52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_zJ/* ch3DataUsage51 */ = new T1(1,_zI/* FormStructure.Chapter3.ch3DataUsage52 */),
_zK/* ch3DataUsage33 */ = {_:0,a:_zJ/* FormStructure.Chapter3.ch3DataUsage51 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_zH/* FormStructure.Chapter3.ch3DataUsage50 */,d:_zG/* FormStructure.Chapter3.ch3DataUsage46 */,e:_zC/* FormStructure.Chapter3.ch3DataUsage44 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_zA/* FormStructure.Chapter3.ch3DataUsage34 */},
_zL/* ch3DataUsage32 */ = new T2(3,_zK/* FormStructure.Chapter3.ch3DataUsage33 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_zM/* ch3DataUsage18 */ = new T2(1,_zL/* FormStructure.Chapter3.ch3DataUsage32 */,_zo/* FormStructure.Chapter3.ch3DataUsage19 */),
_zN/* ch3DataUsage56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_zO/* ch3DataUsage55 */ = new T1(1,_zN/* FormStructure.Chapter3.ch3DataUsage56 */),
_zP/* ch3DataUsage59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_zQ/* ch3DataUsage58 */ = new T2(1,_zP/* FormStructure.Chapter3.ch3DataUsage59 */,_I/* GHC.Types.[] */),
_zR/* ch3DataUsage57 */ = new T2(1,_zF/* FormStructure.Chapter3.ch3DataUsage49 */,_zQ/* FormStructure.Chapter3.ch3DataUsage58 */),
_zS/* ch3DataUsage60 */ = new T1(1,_zv/* FormStructure.Chapter3.ch3DataUsage42 */),
_zT/* ch3DataUsage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_zU/* ch3DataUsage61 */ = new T1(1,_zT/* FormStructure.Chapter3.ch3DataUsage62 */),
_zV/* ch3DataUsage54 */ = {_:0,a:_zU/* FormStructure.Chapter3.ch3DataUsage61 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_zS/* FormStructure.Chapter3.ch3DataUsage60 */,d:_zR/* FormStructure.Chapter3.ch3DataUsage57 */,e:_zO/* FormStructure.Chapter3.ch3DataUsage55 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_zA/* FormStructure.Chapter3.ch3DataUsage34 */},
_zW/* ch3DataUsage53 */ = new T2(3,_zV/* FormStructure.Chapter3.ch3DataUsage54 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_zX/* ch3DataUsage17 */ = new T2(1,_zW/* FormStructure.Chapter3.ch3DataUsage53 */,_zM/* FormStructure.Chapter3.ch3DataUsage18 */),
_zY/* ch3DataUsage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_zZ/* ch3DataUsage65 */ = new T2(1,_zY/* FormStructure.Chapter3.ch3DataUsage66 */,_I/* GHC.Types.[] */),
_A0/* ch3DataUsage67 */ = new T1(1,_zx/* FormStructure.Chapter3.ch3DataUsage43 */),
_A1/* ch3DataUsage69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_A2/* ch3DataUsage68 */ = new T1(1,_A1/* FormStructure.Chapter3.ch3DataUsage69 */),
_A3/* ch3DataUsage64 */ = {_:0,a:_A2/* FormStructure.Chapter3.ch3DataUsage68 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_A0/* FormStructure.Chapter3.ch3DataUsage67 */,d:_zZ/* FormStructure.Chapter3.ch3DataUsage65 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_zA/* FormStructure.Chapter3.ch3DataUsage34 */},
_A4/* ch3DataUsage63 */ = new T2(3,_A3/* FormStructure.Chapter3.ch3DataUsage64 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_A5/* ch3DataUsage16 */ = new T2(1,_A4/* FormStructure.Chapter3.ch3DataUsage63 */,_zX/* FormStructure.Chapter3.ch3DataUsage17 */),
_A6/* ch3DataUsage73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_A7/* ch3DataUsage72 */ = new T1(1,_A6/* FormStructure.Chapter3.ch3DataUsage73 */),
_A8/* ch3DataUsage71 */ = {_:0,a:_A7/* FormStructure.Chapter3.ch3DataUsage72 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_A9/* ch3DataUsage15 */ = new T3(8,_A8/* FormStructure.Chapter3.ch3DataUsage71 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_A5/* FormStructure.Chapter3.ch3DataUsage16 */),
_Aa/* ch3DataUsage13 */ = new T2(1,_A9/* FormStructure.Chapter3.ch3DataUsage15 */,_zj/* FormStructure.Chapter3.ch3DataUsage14 */),
_Ab/* ch3DataUsage104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_Ac/* ch3DataUsage103 */ = new T1(1,_Ab/* FormStructure.Chapter3.ch3DataUsage104 */),
_Ad/* ch3DataUsage106 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_Ae/* ch3DataUsage105 */ = new T1(1,_Ad/* FormStructure.Chapter3.ch3DataUsage106 */),
_Af/* ch3DataUsage102 */ = {_:0,a:_Ae/* FormStructure.Chapter3.ch3DataUsage105 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Ac/* FormStructure.Chapter3.ch3DataUsage103 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ag/* ch3DataUsage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_Ah/* ch3DataUsage82 */ = new T1(0,_Ag/* FormStructure.Chapter3.ch3DataUsage83 */),
_Ai/* ch3DataUsage81 */ = new T2(1,_Ah/* FormStructure.Chapter3.ch3DataUsage82 */,_I/* GHC.Types.[] */),
_Aj/* ch3DataUsage85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_Ak/* ch3DataUsage84 */ = new T1(0,_Aj/* FormStructure.Chapter3.ch3DataUsage85 */),
_Al/* ch3DataUsage80 */ = new T2(1,_Ak/* FormStructure.Chapter3.ch3DataUsage84 */,_Ai/* FormStructure.Chapter3.ch3DataUsage81 */),
_Am/* ch3DataUsage87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_An/* ch3DataUsage86 */ = new T1(0,_Am/* FormStructure.Chapter3.ch3DataUsage87 */),
_Ao/* ch3DataUsage79 */ = new T2(1,_An/* FormStructure.Chapter3.ch3DataUsage86 */,_Al/* FormStructure.Chapter3.ch3DataUsage80 */),
_Ap/* ch3DataUsage89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_Aq/* ch3DataUsage88 */ = new T1(0,_Ap/* FormStructure.Chapter3.ch3DataUsage89 */),
_Ar/* ch3DataUsage78 */ = new T2(1,_Aq/* FormStructure.Chapter3.ch3DataUsage88 */,_Ao/* FormStructure.Chapter3.ch3DataUsage79 */),
_As/* ch3DataUsage92 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_At/* ch3DataUsage91 */ = new T1(1,_As/* FormStructure.Chapter3.ch3DataUsage92 */),
_Au/* ch3DataUsage94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_Av/* ch3DataUsage93 */ = new T1(1,_Au/* FormStructure.Chapter3.ch3DataUsage94 */),
_Aw/* ch3DataUsage90 */ = {_:0,a:_Av/* FormStructure.Chapter3.ch3DataUsage93 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_At/* FormStructure.Chapter3.ch3DataUsage91 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ax/* ch3DataUsage77 */ = new T2(5,_Aw/* FormStructure.Chapter3.ch3DataUsage90 */,_Ar/* FormStructure.Chapter3.ch3DataUsage78 */),
_Ay/* ch3DataUsage76 */ = new T2(1,_Ax/* FormStructure.Chapter3.ch3DataUsage77 */,_I/* GHC.Types.[] */),
_Az/* ch3DataUsage98 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_AA/* ch3DataUsage97 */ = new T1(0,_Az/* FormStructure.Chapter3.ch3DataUsage98 */),
_AB/* ch3DataUsage96 */ = new T2(1,_AA/* FormStructure.Chapter3.ch3DataUsage97 */,_xZ/* FormStructure.Chapter3.ch3DataUsage4 */),
_AC/* ch3DataUsage101 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_AD/* ch3DataUsage100 */ = new T1(1,_AC/* FormStructure.Chapter3.ch3DataUsage101 */),
_AE/* ch3DataUsage99 */ = {_:0,a:_AD/* FormStructure.Chapter3.ch3DataUsage100 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_AF/* ch3DataUsage95 */ = new T2(5,_AE/* FormStructure.Chapter3.ch3DataUsage99 */,_AB/* FormStructure.Chapter3.ch3DataUsage96 */),
_AG/* ch3DataUsage75 */ = new T2(1,_AF/* FormStructure.Chapter3.ch3DataUsage95 */,_Ay/* FormStructure.Chapter3.ch3DataUsage76 */),
_AH/* ch3DataUsage74 */ = new T3(8,_Af/* FormStructure.Chapter3.ch3DataUsage102 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_AG/* FormStructure.Chapter3.ch3DataUsage75 */),
_AI/* ch3DataUsage12 */ = new T2(1,_AH/* FormStructure.Chapter3.ch3DataUsage74 */,_Aa/* FormStructure.Chapter3.ch3DataUsage13 */),
_AJ/* ch3DataUsage11 */ = new T2(1,_zi/* FormStructure.Chapter3.ch3DataUsage107 */,_AI/* FormStructure.Chapter3.ch3DataUsage12 */),
_AK/* ch3DataUsage174 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_AL/* ch3DataUsage173 */ = new T2(1,_AK/* FormStructure.Chapter3.ch3DataUsage174 */,_I/* GHC.Types.[] */),
_AM/* ch3DataUsage175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_AN/* ch3DataUsage172 */ = new T2(1,_AM/* FormStructure.Chapter3.ch3DataUsage175 */,_AL/* FormStructure.Chapter3.ch3DataUsage173 */),
_AO/* ch3DataUsage176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_AP/* ch3DataUsage171 */ = new T2(1,_AO/* FormStructure.Chapter3.ch3DataUsage176 */,_AN/* FormStructure.Chapter3.ch3DataUsage172 */),
_AQ/* ch3DataUsage177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_AR/* ch3DataUsage170 */ = new T2(1,_AQ/* FormStructure.Chapter3.ch3DataUsage177 */,_AP/* FormStructure.Chapter3.ch3DataUsage171 */),
_AS/* ch3DataUsage169 */ = new T1(1,_AR/* FormStructure.Chapter3.ch3DataUsage170 */),
_AT/* ch3DataUsage179 */ = new T2(1,_q5/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_AU/* ch3DataUsage181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_AV/* ch3DataUsage180 */ = new T1(1,_AU/* FormStructure.Chapter3.ch3DataUsage181 */),
_AW/* ch3DataUsage183 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_AX/* ch3DataUsage182 */ = new T2(1,_AW/* FormStructure.Chapter3.ch3DataUsage183 */,_I/* GHC.Types.[] */),
_AY/* ch3DataUsage185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_AZ/* ch3DataUsage184 */ = new T1(1,_AY/* FormStructure.Chapter3.ch3DataUsage185 */),
_B0/* ch3DataUsage187 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_B1/* ch3DataUsage186 */ = new T1(1,_B0/* FormStructure.Chapter3.ch3DataUsage187 */),
_B2/* ch3DataUsage178 */ = {_:0,a:_B1/* FormStructure.Chapter3.ch3DataUsage186 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_AZ/* FormStructure.Chapter3.ch3DataUsage184 */,d:_AX/* FormStructure.Chapter3.ch3DataUsage182 */,e:_AV/* FormStructure.Chapter3.ch3DataUsage180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_AT/* FormStructure.Chapter3.ch3DataUsage179 */},
_B3/* ch3DataUsage168 */ = new T2(3,_B2/* FormStructure.Chapter3.ch3DataUsage178 */,_AS/* FormStructure.Chapter3.ch3DataUsage169 */),
_B4/* ch3DataUsage167 */ = new T2(1,_B3/* FormStructure.Chapter3.ch3DataUsage168 */,_I/* GHC.Types.[] */),
_B5/* ch3DataUsage190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_B6/* ch3DataUsage189 */ = new T1(1,_B5/* FormStructure.Chapter3.ch3DataUsage190 */),
_B7/* ch3DataUsage188 */ = {_:0,a:_B6/* FormStructure.Chapter3.ch3DataUsage189 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_B8/* ch3DataUsage166 */ = new T3(8,_B7/* FormStructure.Chapter3.ch3DataUsage188 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_B4/* FormStructure.Chapter3.ch3DataUsage167 */),
_B9/* ch3DataUsage10 */ = new T2(1,_B8/* FormStructure.Chapter3.ch3DataUsage166 */,_AJ/* FormStructure.Chapter3.ch3DataUsage11 */),
_Ba/* ch3DataUsage207 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-sum"));
}),
_Bb/* ch3DataUsage206 */ = new T1(1,_Ba/* FormStructure.Chapter3.ch3DataUsage207 */),
_Bc/* ch3DataUsage205 */ = {_:0,a:_yi/* FormStructure.Chapter3.ch3DataUsage30 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_Bb/* FormStructure.Chapter3.ch3DataUsage206 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_yg/* FormStructure.Chapter3.ch3DataUsage24 */},
_Bd/* ch3DataUsage204 */ = new T2(3,_Bc/* FormStructure.Chapter3.ch3DataUsage205 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_Be/* ch3DataUsage203 */ = new T2(1,_Bd/* FormStructure.Chapter3.ch3DataUsage204 */,_I/* GHC.Types.[] */),
_Bf/* ch3DataUsage215 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-worldwide"));
}),
_Bg/* ch3DataUsage214 */ = new T2(1,_Bf/* FormStructure.Chapter3.ch3DataUsage215 */,_I/* GHC.Types.[] */),
_Bh/* ch3DataUsage216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-european"));
}),
_Bi/* ch3DataUsage213 */ = new T2(1,_Bh/* FormStructure.Chapter3.ch3DataUsage216 */,_Bg/* FormStructure.Chapter3.ch3DataUsage214 */),
_Bj/* ch3DataUsage217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-national"));
}),
_Bk/* ch3DataUsage212 */ = new T2(1,_Bj/* FormStructure.Chapter3.ch3DataUsage217 */,_Bi/* FormStructure.Chapter3.ch3DataUsage213 */),
_Bl/* ch3DataUsage218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-institutional"));
}),
_Bm/* ch3DataUsage211 */ = new T2(1,_Bl/* FormStructure.Chapter3.ch3DataUsage218 */,_Bk/* FormStructure.Chapter3.ch3DataUsage212 */),
_Bn/* ch3DataUsage_fundingSumRule1 */ = new T2(0,_Bm/* FormStructure.Chapter3.ch3DataUsage211 */,_Ba/* FormStructure.Chapter3.ch3DataUsage207 */),
_Bo/* ch3DataUsage210 */ = new T2(1,_Bn/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule1 */,_ys/* FormStructure.Chapter3.ch3DataUsage123 */),
_Bp/* ch3DataUsage219 */ = new T1(1,_Bf/* FormStructure.Chapter3.ch3DataUsage215 */),
_Bq/* ch3DataUsage209 */ = {_:0,a:_yF/* FormStructure.Chapter3.ch3DataUsage135 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_Bp/* FormStructure.Chapter3.ch3DataUsage219 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_Bo/* FormStructure.Chapter3.ch3DataUsage210 */},
_Br/* ch3DataUsage208 */ = new T2(3,_Bq/* FormStructure.Chapter3.ch3DataUsage209 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bs/* ch3DataUsage202 */ = new T2(1,_Br/* FormStructure.Chapter3.ch3DataUsage208 */,_Be/* FormStructure.Chapter3.ch3DataUsage203 */),
_Bt/* ch3DataUsage222 */ = new T1(1,_Bh/* FormStructure.Chapter3.ch3DataUsage216 */),
_Bu/* ch3DataUsage221 */ = {_:0,a:_yL/* FormStructure.Chapter3.ch3DataUsage140 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_Bt/* FormStructure.Chapter3.ch3DataUsage222 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_Bo/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bv/* ch3DataUsage220 */ = new T2(3,_Bu/* FormStructure.Chapter3.ch3DataUsage221 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bw/* ch3DataUsage201 */ = new T2(1,_Bv/* FormStructure.Chapter3.ch3DataUsage220 */,_Bs/* FormStructure.Chapter3.ch3DataUsage202 */),
_Bx/* ch3DataUsage225 */ = new T1(1,_Bj/* FormStructure.Chapter3.ch3DataUsage217 */),
_By/* ch3DataUsage224 */ = {_:0,a:_yR/* FormStructure.Chapter3.ch3DataUsage145 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_Bx/* FormStructure.Chapter3.ch3DataUsage225 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_Bo/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bz/* ch3DataUsage223 */ = new T2(3,_By/* FormStructure.Chapter3.ch3DataUsage224 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_BA/* ch3DataUsage200 */ = new T2(1,_Bz/* FormStructure.Chapter3.ch3DataUsage223 */,_Bw/* FormStructure.Chapter3.ch3DataUsage201 */),
_BB/* ch3DataUsage228 */ = new T1(1,_Bl/* FormStructure.Chapter3.ch3DataUsage218 */),
_BC/* ch3DataUsage227 */ = {_:0,a:_yX/* FormStructure.Chapter3.ch3DataUsage150 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_BB/* FormStructure.Chapter3.ch3DataUsage228 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_Bo/* FormStructure.Chapter3.ch3DataUsage210 */},
_BD/* ch3DataUsage226 */ = new T2(3,_BC/* FormStructure.Chapter3.ch3DataUsage227 */,_yl/* FormStructure.Chapter3.ch3DataUsage21 */),
_BE/* ch3DataUsage199 */ = new T2(1,_BD/* FormStructure.Chapter3.ch3DataUsage226 */,_BA/* FormStructure.Chapter3.ch3DataUsage200 */),
_BF/* ch3DataUsage198 */ = new T3(8,_z3/* FormStructure.Chapter3.ch3DataUsage152 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_BE/* FormStructure.Chapter3.ch3DataUsage199 */),
_BG/* ch3DataUsage197 */ = new T2(1,_BF/* FormStructure.Chapter3.ch3DataUsage198 */,_I/* GHC.Types.[] */),
_BH/* ch3DataUsage196 */ = new T2(1,_zb/* FormStructure.Chapter3.ch3DataUsage155 */,_BG/* FormStructure.Chapter3.ch3DataUsage197 */),
_BI/* ch3DataUsage231 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_BJ/* ch3DataUsage230 */ = new T1(1,_BI/* FormStructure.Chapter3.ch3DataUsage231 */),
_BK/* ch3DataUsage229 */ = {_:0,a:_BJ/* FormStructure.Chapter3.ch3DataUsage230 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_BL/* ch3DataUsage195 */ = new T3(8,_BK/* FormStructure.Chapter3.ch3DataUsage229 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_BH/* FormStructure.Chapter3.ch3DataUsage196 */),
_BM/* ch3DataUsage194 */ = new T2(1,_BL/* FormStructure.Chapter3.ch3DataUsage195 */,_I/* GHC.Types.[] */),
_BN/* ch3DataUsage235 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_BO/* ch3DataUsage234 */ = new T1(1,_BN/* FormStructure.Chapter3.ch3DataUsage235 */),
_BP/* ch3DataUsage237 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_3"));
}),
_BQ/* ch3DataUsage236 */ = new T2(1,_BP/* FormStructure.Chapter3.ch3DataUsage237 */,_I/* GHC.Types.[] */),
_BR/* ch3DataUsage239 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific primary data volume"));
}),
_BS/* ch3DataUsage238 */ = new T1(1,_BR/* FormStructure.Chapter3.ch3DataUsage239 */),
_BT/* ch3DataUsage233 */ = {_:0,a:_BS/* FormStructure.Chapter3.ch3DataUsage238 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_BQ/* FormStructure.Chapter3.ch3DataUsage236 */,e:_BO/* FormStructure.Chapter3.ch3DataUsage234 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_BU/* ch3DataUsage232 */ = new T2(3,_BT/* FormStructure.Chapter3.ch3DataUsage233 */,_AS/* FormStructure.Chapter3.ch3DataUsage169 */),
_BV/* ch3DataUsage193 */ = new T2(1,_BU/* FormStructure.Chapter3.ch3DataUsage232 */,_BM/* FormStructure.Chapter3.ch3DataUsage194 */),
_BW/* ch3DataUsage241 */ = new T1(0,_AM/* FormStructure.Chapter3.ch3DataUsage175 */),
_BX/* ch3DataUsage243 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_BY/* ch3DataUsage245 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_BZ/* ch3DataUsage244 */ = new T2(1,_BY/* FormStructure.Chapter3.ch3DataUsage245 */,_I/* GHC.Types.[] */),
_C0/* ch3DataUsage247 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_C1/* ch3DataUsage246 */ = new T1(1,_C0/* FormStructure.Chapter3.ch3DataUsage247 */),
_C2/* ch3DataUsage249 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_C3/* ch3DataUsage248 */ = new T1(1,_C2/* FormStructure.Chapter3.ch3DataUsage249 */),
_C4/* ch3DataUsage242 */ = {_:0,a:_C3/* FormStructure.Chapter3.ch3DataUsage248 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_C1/* FormStructure.Chapter3.ch3DataUsage246 */,d:_BZ/* FormStructure.Chapter3.ch3DataUsage244 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_BX/* FormStructure.Chapter3.ch3DataUsage243 */},
_C5/* ch3DataUsage240 */ = new T2(3,_C4/* FormStructure.Chapter3.ch3DataUsage242 */,_BW/* FormStructure.Chapter3.ch3DataUsage241 */),
_C6/* ch3DataUsage192 */ = new T2(1,_C5/* FormStructure.Chapter3.ch3DataUsage240 */,_BV/* FormStructure.Chapter3.ch3DataUsage193 */),
_C7/* ch3DataUsage252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_C8/* ch3DataUsage251 */ = new T1(1,_C7/* FormStructure.Chapter3.ch3DataUsage252 */),
_C9/* ch3DataUsage250 */ = {_:0,a:_C8/* FormStructure.Chapter3.ch3DataUsage251 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ca/* ch3DataUsage191 */ = new T3(8,_C9/* FormStructure.Chapter3.ch3DataUsage250 */,_y8/* FormStructure.Chapter3.ch3DataUsage70 */,_C6/* FormStructure.Chapter3.ch3DataUsage192 */),
_Cb/* ch3DataUsage9 */ = new T2(1,_Ca/* FormStructure.Chapter3.ch3DataUsage191 */,_B9/* FormStructure.Chapter3.ch3DataUsage10 */),
_Cc/* ch3DataUsage8 */ = new T2(1,_y9/* FormStructure.Chapter3.ch3DataUsage253 */,_Cb/* FormStructure.Chapter3.ch3DataUsage9 */),
_Cd/* ch3DataUsage7 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_Az/* FormStructure.Chapter3.ch3DataUsage98 */,_Cc/* FormStructure.Chapter3.ch3DataUsage8 */),
_Ce/* ch3DataUsage3 */ = new T2(1,_Cd/* FormStructure.Chapter3.ch3DataUsage7 */,_xZ/* FormStructure.Chapter3.ch3DataUsage4 */),
_Cf/* ch3DataUsage2 */ = new T2(5,_xW/* FormStructure.Chapter3.ch3DataUsage262 */,_Ce/* FormStructure.Chapter3.ch3DataUsage3 */),
_Cg/* ch3DataUsage1 */ = new T2(1,_Cf/* FormStructure.Chapter3.ch3DataUsage2 */,_I/* GHC.Types.[] */),
_Ch/* ch3DataUsage267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("3.Usage "));
}),
_Ci/* ch3DataUsage266 */ = new T1(1,_Ch/* FormStructure.Chapter3.ch3DataUsage267 */),
_Cj/* ch3DataUsage265 */ = {_:0,a:_Ci/* FormStructure.Chapter3.ch3DataUsage266 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ck/* ch3DataUsage */ = new T2(7,_Cj/* FormStructure.Chapter3.ch3DataUsage265 */,_Cg/* FormStructure.Chapter3.ch3DataUsage1 */),
_Cl/* ch4DataStorage3 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_Cm/* ch4DataStorage46 */ = 0,
_Cn/* ch4DataStorage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage providers"));
}),
_Co/* ch4DataStorage48 */ = new T1(1,_Cn/* FormStructure.Chapter4.ch4DataStorage49 */),
_Cp/* ch4DataStorage47 */ = {_:0,a:_Co/* FormStructure.Chapter4.ch4DataStorage48 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Cq/* ch4DataStorage11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_Cr/* ch4DataStorage10 */ = new T1(0,_Cq/* FormStructure.Chapter4.ch4DataStorage11 */),
_Cs/* ch4DataStorage26 */ = function(_Ct/* s6w8 */){
  var _Cu/* s6w9 */ = E(_Ct/* s6w8 */);
  return (_Cu/* s6w9 */<0) ? false : _Cu/* s6w9 */<=100;
},
_Cv/* ch4DataStorage25 */ = new T1(4,_Cs/* FormStructure.Chapter4.ch4DataStorage26 */),
_Cw/* ch4DataStorage24 */ = new T2(1,_Cv/* FormStructure.Chapter4.ch4DataStorage25 */,_I/* GHC.Types.[] */),
_Cx/* ch4DataStorage18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-providers-sum"));
}),
_Cy/* ch4DataStorage30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-external"));
}),
_Cz/* ch4DataStorage29 */ = new T2(1,_Cy/* FormStructure.Chapter4.ch4DataStorage30 */,_I/* GHC.Types.[] */),
_CA/* ch4DataStorage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-institutional"));
}),
_CB/* ch4DataStorage28 */ = new T2(1,_CA/* FormStructure.Chapter4.ch4DataStorage31 */,_Cz/* FormStructure.Chapter4.ch4DataStorage29 */),
_CC/* ch4DataStorage32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-group"));
}),
_CD/* ch4DataStorage27 */ = new T2(1,_CC/* FormStructure.Chapter4.ch4DataStorage32 */,_CB/* FormStructure.Chapter4.ch4DataStorage28 */),
_CE/* ch4DataStorage_storageSumRule */ = new T2(0,_CD/* FormStructure.Chapter4.ch4DataStorage27 */,_Cx/* FormStructure.Chapter4.ch4DataStorage18 */),
_CF/* ch4DataStorage23 */ = new T2(1,_CE/* FormStructure.Chapter4.ch4DataStorage_storageSumRule */,_Cw/* FormStructure.Chapter4.ch4DataStorage24 */),
_CG/* ch4DataStorage43 */ = new T1(1,_CC/* FormStructure.Chapter4.ch4DataStorage32 */),
_CH/* ch4DataStorage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Group\'s local"));
}),
_CI/* ch4DataStorage44 */ = new T1(1,_CH/* FormStructure.Chapter4.ch4DataStorage45 */),
_CJ/* ch4DataStorage42 */ = {_:0,a:_CI/* FormStructure.Chapter4.ch4DataStorage44 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_CG/* FormStructure.Chapter4.ch4DataStorage43 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_CF/* FormStructure.Chapter4.ch4DataStorage23 */},
_CK/* ch4DataStorage41 */ = new T2(3,_CJ/* FormStructure.Chapter4.ch4DataStorage42 */,_Cr/* FormStructure.Chapter4.ch4DataStorage10 */),
_CL/* ch4DataStorage38 */ = new T1(1,_CA/* FormStructure.Chapter4.ch4DataStorage31 */),
_CM/* ch4DataStorage40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_CN/* ch4DataStorage39 */ = new T1(1,_CM/* FormStructure.Chapter4.ch4DataStorage40 */),
_CO/* ch4DataStorage37 */ = {_:0,a:_CN/* FormStructure.Chapter4.ch4DataStorage39 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_CL/* FormStructure.Chapter4.ch4DataStorage38 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_CF/* FormStructure.Chapter4.ch4DataStorage23 */},
_CP/* ch4DataStorage36 */ = new T2(3,_CO/* FormStructure.Chapter4.ch4DataStorage37 */,_Cr/* FormStructure.Chapter4.ch4DataStorage10 */),
_CQ/* ch4DataStorage33 */ = new T1(1,_Cy/* FormStructure.Chapter4.ch4DataStorage30 */),
_CR/* ch4DataStorage35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External Provider"));
}),
_CS/* ch4DataStorage34 */ = new T1(1,_CR/* FormStructure.Chapter4.ch4DataStorage35 */),
_CT/* ch4DataStorage22 */ = {_:0,a:_CS/* FormStructure.Chapter4.ch4DataStorage34 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_CQ/* FormStructure.Chapter4.ch4DataStorage33 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_CF/* FormStructure.Chapter4.ch4DataStorage23 */},
_CU/* ch4DataStorage21 */ = new T2(3,_CT/* FormStructure.Chapter4.ch4DataStorage22 */,_Cr/* FormStructure.Chapter4.ch4DataStorage10 */),
_CV/* ch4DataStorage16 */ = function(_CW/* s6we */){
  return E(_CW/* s6we */)==100;
},
_CX/* ch4DataStorage15 */ = new T1(4,_CV/* FormStructure.Chapter4.ch4DataStorage16 */),
_CY/* ch4DataStorage14 */ = new T2(1,_CX/* FormStructure.Chapter4.ch4DataStorage15 */,_I/* GHC.Types.[] */),
_CZ/* ch4DataStorage13 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_CY/* FormStructure.Chapter4.ch4DataStorage14 */),
_D0/* ch4DataStorage17 */ = new T1(1,_Cx/* FormStructure.Chapter4.ch4DataStorage18 */),
_D1/* ch4DataStorage20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_D2/* ch4DataStorage19 */ = new T1(1,_D1/* FormStructure.Chapter4.ch4DataStorage20 */),
_D3/* ch4DataStorage12 */ = {_:0,a:_D2/* FormStructure.Chapter4.ch4DataStorage19 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_D0/* FormStructure.Chapter4.ch4DataStorage17 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_CZ/* FormStructure.Chapter4.ch4DataStorage13 */},
_D4/* ch4DataStorage9 */ = new T2(3,_D3/* FormStructure.Chapter4.ch4DataStorage12 */,_Cr/* FormStructure.Chapter4.ch4DataStorage10 */),
_D5/* ch4DataStorage8 */ = new T2(1,_D4/* FormStructure.Chapter4.ch4DataStorage9 */,_I/* GHC.Types.[] */),
_D6/* ch4DataStorage7 */ = new T2(1,_CU/* FormStructure.Chapter4.ch4DataStorage21 */,_D5/* FormStructure.Chapter4.ch4DataStorage8 */),
_D7/* ch4DataStorage6 */ = new T2(1,_CP/* FormStructure.Chapter4.ch4DataStorage36 */,_D6/* FormStructure.Chapter4.ch4DataStorage7 */),
_D8/* ch4DataStorage5 */ = new T2(1,_CK/* FormStructure.Chapter4.ch4DataStorage41 */,_D7/* FormStructure.Chapter4.ch4DataStorage6 */),
_D9/* ch4DataStorage4 */ = new T3(8,_Cp/* FormStructure.Chapter4.ch4DataStorage47 */,_Cm/* FormStructure.Chapter4.ch4DataStorage46 */,_D8/* FormStructure.Chapter4.ch4DataStorage5 */),
_Da/* ch4DataStorage2 */ = new T2(1,_D9/* FormStructure.Chapter4.ch4DataStorage4 */,_Cl/* FormStructure.Chapter4.ch4DataStorage3 */),
_Db/* ch4DataStorage60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_Dc/* ch4DataStorage59 */ = new T2(1,_Db/* FormStructure.Chapter4.ch4DataStorage60 */,_I/* GHC.Types.[] */),
_Dd/* ch4DataStorage61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_De/* ch4DataStorage58 */ = new T2(1,_Dd/* FormStructure.Chapter4.ch4DataStorage61 */,_Dc/* FormStructure.Chapter4.ch4DataStorage59 */),
_Df/* ch4DataStorage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_Dg/* ch4DataStorage57 */ = new T2(1,_Df/* FormStructure.Chapter4.ch4DataStorage62 */,_De/* FormStructure.Chapter4.ch4DataStorage58 */),
_Dh/* ch4DataStorage63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_Di/* ch4DataStorage56 */ = new T2(1,_Dh/* FormStructure.Chapter4.ch4DataStorage63 */,_Dg/* FormStructure.Chapter4.ch4DataStorage57 */),
_Dj/* ch4DataStorage55 */ = new T1(1,_Di/* FormStructure.Chapter4.ch4DataStorage56 */),
_Dk/* ch4DataStorage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of backups"));
}),
_Dl/* ch4DataStorage65 */ = new T1(1,_Dk/* FormStructure.Chapter4.ch4DataStorage66 */),
_Dm/* ch4DataStorage64 */ = {_:0,a:_Dl/* FormStructure.Chapter4.ch4DataStorage65 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Dn/* ch4DataStorage54 */ = new T2(3,_Dm/* FormStructure.Chapter4.ch4DataStorage64 */,_Dj/* FormStructure.Chapter4.ch4DataStorage55 */),
_Do/* ch4DataStorage53 */ = new T2(1,_Dn/* FormStructure.Chapter4.ch4DataStorage54 */,_I/* GHC.Types.[] */),
_Dp/* ch4DataStorage70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of data stored at the end of 2015"));
}),
_Dq/* ch4DataStorage69 */ = new T1(1,_Dp/* FormStructure.Chapter4.ch4DataStorage70 */),
_Dr/* ch4DataStorage68 */ = {_:0,a:_Dq/* FormStructure.Chapter4.ch4DataStorage69 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ds/* ch4DataStorage67 */ = new T2(3,_Dr/* FormStructure.Chapter4.ch4DataStorage68 */,_Dj/* FormStructure.Chapter4.ch4DataStorage55 */),
_Dt/* ch4DataStorage52 */ = new T2(1,_Ds/* FormStructure.Chapter4.ch4DataStorage67 */,_Do/* FormStructure.Chapter4.ch4DataStorage53 */),
_Du/* ch4DataStorage72 */ = new T1(0,_Dd/* FormStructure.Chapter4.ch4DataStorage61 */),
_Dv/* ch4DataStorage74 */ = new T2(1,_pJ/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_Dw/* ch4DataStorage76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_Dx/* ch4DataStorage75 */ = new T1(1,_Dw/* FormStructure.Chapter4.ch4DataStorage76 */),
_Dy/* ch4DataStorage78 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume produced in 2015"));
}),
_Dz/* ch4DataStorage77 */ = new T1(1,_Dy/* FormStructure.Chapter4.ch4DataStorage78 */),
_DA/* ch4DataStorage73 */ = {_:0,a:_Dz/* FormStructure.Chapter4.ch4DataStorage77 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_Dx/* FormStructure.Chapter4.ch4DataStorage75 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_Dv/* FormStructure.Chapter4.ch4DataStorage74 */},
_DB/* ch4DataStorage71 */ = new T2(3,_DA/* FormStructure.Chapter4.ch4DataStorage73 */,_Du/* FormStructure.Chapter4.ch4DataStorage72 */),
_DC/* ch4DataStorage51 */ = new T2(1,_DB/* FormStructure.Chapter4.ch4DataStorage71 */,_Dt/* FormStructure.Chapter4.ch4DataStorage52 */),
_DD/* ch4DataStorage81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just scientic data volumes (without backups and scratch/tmp) are in question."));
}),
_DE/* ch4DataStorage80 */ = new T1(1,_DD/* FormStructure.Chapter4.ch4DataStorage81 */),
_DF/* ch4DataStorage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data volumes"));
}),
_DG/* ch4DataStorage82 */ = new T1(1,_DF/* FormStructure.Chapter4.ch4DataStorage83 */),
_DH/* ch4DataStorage79 */ = {_:0,a:_DG/* FormStructure.Chapter4.ch4DataStorage82 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_DE/* FormStructure.Chapter4.ch4DataStorage80 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_DI/* ch4DataStorage50 */ = new T3(8,_DH/* FormStructure.Chapter4.ch4DataStorage79 */,_Cm/* FormStructure.Chapter4.ch4DataStorage46 */,_DC/* FormStructure.Chapter4.ch4DataStorage51 */),
_DJ/* ch4DataStorage1 */ = new T2(1,_DI/* FormStructure.Chapter4.ch4DataStorage50 */,_Da/* FormStructure.Chapter4.ch4DataStorage2 */),
_DK/* ch4DataStorage86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("4.Storage "));
}),
_DL/* ch4DataStorage85 */ = new T1(1,_DK/* FormStructure.Chapter4.ch4DataStorage86 */),
_DM/* ch4DataStorage84 */ = {_:0,a:_DL/* FormStructure.Chapter4.ch4DataStorage85 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_DN/* ch4DataStorage */ = new T2(7,_DM/* FormStructure.Chapter4.ch4DataStorage84 */,_DJ/* FormStructure.Chapter4.ch4DataStorage1 */),
_DO/* ch5DataAccessibility2 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_DP/* ch5DataAccessibility32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you provide data accessibility for external parties?"));
}),
_DQ/* ch5DataAccessibility31 */ = new T1(1,_DP/* FormStructure.Chapter5.ch5DataAccessibility32 */),
_DR/* ch5DataAccessibility30 */ = {_:0,a:_DQ/* FormStructure.Chapter5.ch5DataAccessibility31 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_DS/* ch5DataAccessibility7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_DT/* ch5DataAccessibility6 */ = new T1(0,_DS/* FormStructure.Chapter5.ch5DataAccessibility7 */),
_DU/* ch5DataAccessibility5 */ = new T2(1,_DT/* FormStructure.Chapter5.ch5DataAccessibility6 */,_I/* GHC.Types.[] */),
_DV/* ch5DataAccessibility29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_DW/* ch5DataAccessibility16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("URLs to web pages / data source or other accessibility link"));
}),
_DX/* ch5DataAccessibility15 */ = new T1(1,_DW/* FormStructure.Chapter5.ch5DataAccessibility16 */),
_DY/* ch5DataAccessibility18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Links to your services"));
}),
_DZ/* ch5DataAccessibility17 */ = new T1(1,_DY/* FormStructure.Chapter5.ch5DataAccessibility18 */),
_E0/* ch5DataAccessibility14 */ = {_:0,a:_DZ/* FormStructure.Chapter5.ch5DataAccessibility17 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_DX/* FormStructure.Chapter5.ch5DataAccessibility15 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_E1/* ch5DataAccessibility13 */ = new T1(1,_E0/* FormStructure.Chapter5.ch5DataAccessibility14 */),
_E2/* ch5DataAccessibility12 */ = new T2(1,_E1/* FormStructure.Chapter5.ch5DataAccessibility13 */,_I/* GHC.Types.[] */),
_E3/* ch5DataAccessibility22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For inspiration, click the red box in the figure"));
}),
_E4/* ch5DataAccessibility21 */ = new T1(1,_E3/* FormStructure.Chapter5.ch5DataAccessibility22 */),
_E5/* ch5DataAccessibility24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How do you make your data accessible?"));
}),
_E6/* ch5DataAccessibility23 */ = new T1(1,_E5/* FormStructure.Chapter5.ch5DataAccessibility24 */),
_E7/* ch5DataAccessibility20 */ = {_:0,a:_E6/* FormStructure.Chapter5.ch5DataAccessibility23 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_E4/* FormStructure.Chapter5.ch5DataAccessibility21 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_E8/* ch5DataAccessibility19 */ = new T1(1,_E7/* FormStructure.Chapter5.ch5DataAccessibility20 */),
_E9/* ch5DataAccessibility11 */ = new T2(1,_E8/* FormStructure.Chapter5.ch5DataAccessibility19 */,_E2/* FormStructure.Chapter5.ch5DataAccessibility12 */),
_Ea/* ch5DataAccessibility25 */ = 1,
_Eb/* ch5DataAccessibility28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accessibility details"));
}),
_Ec/* ch5DataAccessibility27 */ = new T1(1,_Eb/* FormStructure.Chapter5.ch5DataAccessibility28 */),
_Ed/* ch5DataAccessibility26 */ = {_:0,a:_Ec/* FormStructure.Chapter5.ch5DataAccessibility27 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ee/* ch5DataAccessibility10 */ = new T3(8,_Ed/* FormStructure.Chapter5.ch5DataAccessibility26 */,_Ea/* FormStructure.Chapter5.ch5DataAccessibility25 */,_E9/* FormStructure.Chapter5.ch5DataAccessibility11 */),
_Ef/* ch5DataAccessibility9 */ = new T2(1,_Ee/* FormStructure.Chapter5.ch5DataAccessibility10 */,_I/* GHC.Types.[] */),
_Eg/* ch5DataAccessibility8 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_DV/* FormStructure.Chapter5.ch5DataAccessibility29 */,_Ef/* FormStructure.Chapter5.ch5DataAccessibility9 */),
_Eh/* ch5DataAccessibility4 */ = new T2(1,_Eg/* FormStructure.Chapter5.ch5DataAccessibility8 */,_DU/* FormStructure.Chapter5.ch5DataAccessibility5 */),
_Ei/* ch5DataAccessibility3 */ = new T2(5,_DR/* FormStructure.Chapter5.ch5DataAccessibility30 */,_Eh/* FormStructure.Chapter5.ch5DataAccessibility4 */),
_Ej/* ch5DataAccessibility1 */ = new T2(1,_Ei/* FormStructure.Chapter5.ch5DataAccessibility3 */,_DO/* FormStructure.Chapter5.ch5DataAccessibility2 */),
_Ek/* ch5DataAccessibility35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("5.Accessibility "));
}),
_El/* ch5DataAccessibility34 */ = new T1(1,_Ek/* FormStructure.Chapter5.ch5DataAccessibility35 */),
_Em/* ch5DataAccessibility33 */ = {_:0,a:_El/* FormStructure.Chapter5.ch5DataAccessibility34 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_En/* ch5DataAccessibility */ = new T2(7,_Em/* FormStructure.Chapter5.ch5DataAccessibility33 */,_Ej/* FormStructure.Chapter5.ch5DataAccessibility1 */),
_Eo/* ch6DataManagement13 */ = 0,
_Ep/* ch6DataManagement28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_Eq/* ch6DataManagement27 */ = new T1(0,_Ep/* FormStructure.Chapter6.ch6DataManagement28 */),
_Er/* ch6DataManagement26 */ = new T2(1,_Eq/* FormStructure.Chapter6.ch6DataManagement27 */,_I/* GHC.Types.[] */),
_Es/* xhow3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How?"));
}),
_Et/* xhow2 */ = new T1(1,_Es/* FormStructure.Common.xhow3 */),
_Eu/* xhow1 */ = {_:0,a:_Et/* FormStructure.Common.xhow2 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ev/* xhow */ = new T1(1,_Eu/* FormStructure.Common.xhow1 */),
_Ew/* ch6DataManagement30 */ = new T2(1,_Ev/* FormStructure.Common.xhow */,_I/* GHC.Types.[] */),
_Ex/* ch6DataManagement31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_Ey/* ch6DataManagement29 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_Ex/* FormStructure.Chapter6.ch6DataManagement31 */,_Ew/* FormStructure.Chapter6.ch6DataManagement30 */),
_Ez/* ch6DataManagement25 */ = new T2(1,_Ey/* FormStructure.Chapter6.ch6DataManagement29 */,_Er/* FormStructure.Chapter6.ch6DataManagement26 */),
_EA/* ch6DataManagement34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you apply some form of data stewardship?"));
}),
_EB/* ch6DataManagement33 */ = new T1(1,_EA/* FormStructure.Chapter6.ch6DataManagement34 */),
_EC/* ch6DataManagement32 */ = {_:0,a:_EB/* FormStructure.Chapter6.ch6DataManagement33 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_ED/* ch6DataManagement24 */ = new T2(5,_EC/* FormStructure.Chapter6.ch6DataManagement32 */,_Ez/* FormStructure.Chapter6.ch6DataManagement25 */),
_EE/* ch6DataManagement23 */ = new T2(1,_ED/* FormStructure.Chapter6.ch6DataManagement24 */,_I/* GHC.Types.[] */),
_EF/* ch6DataManagement37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_EG/* ch6DataManagement36 */ = new T1(0,_EF/* FormStructure.Chapter6.ch6DataManagement37 */),
_EH/* ch6DataManagement40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest required sustainability"));
}),
_EI/* ch6DataManagement39 */ = new T1(1,_EH/* FormStructure.Chapter6.ch6DataManagement40 */),
_EJ/* ch6DataManagement38 */ = {_:0,a:_EI/* FormStructure.Chapter6.ch6DataManagement39 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EK/* ch6DataManagement35 */ = new T2(3,_EJ/* FormStructure.Chapter6.ch6DataManagement38 */,_EG/* FormStructure.Chapter6.ch6DataManagement36 */),
_EL/* ch6DataManagement22 */ = new T2(1,_EK/* FormStructure.Chapter6.ch6DataManagement35 */,_EE/* FormStructure.Chapter6.ch6DataManagement23 */),
_EM/* ch6DataManagement51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long"));
}),
_EN/* ch6DataManagement50 */ = new T1(1,_EM/* FormStructure.Chapter6.ch6DataManagement51 */),
_EO/* ch6DataManagement49 */ = {_:0,a:_EN/* FormStructure.Chapter6.ch6DataManagement50 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EP/* ch6DataManagement48 */ = new T2(3,_EO/* FormStructure.Chapter6.ch6DataManagement49 */,_EG/* FormStructure.Chapter6.ch6DataManagement36 */),
_EQ/* ch6DataManagement47 */ = new T2(1,_EP/* FormStructure.Chapter6.ch6DataManagement48 */,_I/* GHC.Types.[] */),
_ER/* ch6DataManagement52 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_ES/* ch6DataManagement46 */ = new T3(8,_ER/* FormStructure.Chapter6.ch6DataManagement52 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_EQ/* FormStructure.Chapter6.ch6DataManagement47 */),
_ET/* ch6DataManagement45 */ = new T2(1,_ES/* FormStructure.Chapter6.ch6DataManagement46 */,_I/* GHC.Types.[] */),
_EU/* ch6DataManagement53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("short-term"));
}),
_EV/* ch6DataManagement44 */ = new T3(1,_8g/* FormEngine.FormItem.NoNumbering */,_EU/* FormStructure.Chapter6.ch6DataManagement53 */,_ET/* FormStructure.Chapter6.ch6DataManagement45 */),
_EW/* ch6DataManagement43 */ = new T2(1,_EV/* FormStructure.Chapter6.ch6DataManagement44 */,_I/* GHC.Types.[] */),
_EX/* ch6DataManagement55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("long-term, continuous funding"));
}),
_EY/* ch6DataManagement54 */ = new T1(0,_EX/* FormStructure.Chapter6.ch6DataManagement55 */),
_EZ/* ch6DataManagement42 */ = new T2(1,_EY/* FormStructure.Chapter6.ch6DataManagement54 */,_EW/* FormStructure.Chapter6.ch6DataManagement43 */),
_F0/* ch6DataManagement58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sustainability"));
}),
_F1/* ch6DataManagement57 */ = new T1(1,_F0/* FormStructure.Chapter6.ch6DataManagement58 */),
_F2/* ch6DataManagement56 */ = {_:0,a:_F1/* FormStructure.Chapter6.ch6DataManagement57 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_F3/* ch6DataManagement41 */ = new T2(5,_F2/* FormStructure.Chapter6.ch6DataManagement56 */,_EZ/* FormStructure.Chapter6.ch6DataManagement42 */),
_F4/* ch6DataManagement21 */ = new T2(1,_F3/* FormStructure.Chapter6.ch6DataManagement41 */,_EL/* FormStructure.Chapter6.ch6DataManagement22 */),
_F5/* ch6DataManagement63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("yes"));
}),
_F6/* ch6DataManagement62 */ = new T1(0,_F5/* FormStructure.Chapter6.ch6DataManagement63 */),
_F7/* ch6DataManagement61 */ = new T2(1,_F6/* FormStructure.Chapter6.ch6DataManagement62 */,_I/* GHC.Types.[] */),
_F8/* ch6DataManagement65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("no"));
}),
_F9/* ch6DataManagement64 */ = new T1(0,_F8/* FormStructure.Chapter6.ch6DataManagement65 */),
_Fa/* ch6DataManagement60 */ = new T2(1,_F9/* FormStructure.Chapter6.ch6DataManagement64 */,_F7/* FormStructure.Chapter6.ch6DataManagement61 */),
_Fb/* ch6DataManagement68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is data actuality maintained (updates)?"));
}),
_Fc/* ch6DataManagement67 */ = new T1(1,_Fb/* FormStructure.Chapter6.ch6DataManagement68 */),
_Fd/* ch6DataManagement66 */ = {_:0,a:_Fc/* FormStructure.Chapter6.ch6DataManagement67 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fe/* ch6DataManagement59 */ = new T2(5,_Fd/* FormStructure.Chapter6.ch6DataManagement66 */,_Fa/* FormStructure.Chapter6.ch6DataManagement60 */),
_Ff/* ch6DataManagement20 */ = new T2(1,_Fe/* FormStructure.Chapter6.ch6DataManagement59 */,_F4/* FormStructure.Chapter6.ch6DataManagement21 */),
_Fg/* ch6DataManagement72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you manage versioning?"));
}),
_Fh/* ch6DataManagement71 */ = new T1(1,_Fg/* FormStructure.Chapter6.ch6DataManagement72 */),
_Fi/* ch6DataManagement70 */ = {_:0,a:_Fh/* FormStructure.Chapter6.ch6DataManagement71 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fj/* ch6DataManagement69 */ = new T2(5,_Fi/* FormStructure.Chapter6.ch6DataManagement70 */,_Fa/* FormStructure.Chapter6.ch6DataManagement60 */),
_Fk/* ch6DataManagement19 */ = new T2(1,_Fj/* FormStructure.Chapter6.ch6DataManagement69 */,_Ff/* FormStructure.Chapter6.ch6DataManagement20 */),
_Fl/* ch6DataManagement76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you handle error reports?"));
}),
_Fm/* ch6DataManagement75 */ = new T1(1,_Fl/* FormStructure.Chapter6.ch6DataManagement76 */),
_Fn/* ch6DataManagement74 */ = {_:0,a:_Fm/* FormStructure.Chapter6.ch6DataManagement75 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fo/* ch6DataManagement73 */ = new T2(5,_Fn/* FormStructure.Chapter6.ch6DataManagement74 */,_Fa/* FormStructure.Chapter6.ch6DataManagement60 */),
_Fp/* ch6DataManagement18 */ = new T2(1,_Fo/* FormStructure.Chapter6.ch6DataManagement73 */,_Fk/* FormStructure.Chapter6.ch6DataManagement19 */),
_Fq/* ch6DataManagement79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Management details"));
}),
_Fr/* ch6DataManagement78 */ = new T1(1,_Fq/* FormStructure.Chapter6.ch6DataManagement79 */),
_Fs/* ch6DataManagement77 */ = {_:0,a:_Fr/* FormStructure.Chapter6.ch6DataManagement78 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ft/* ch6DataManagement17 */ = new T3(8,_Fs/* FormStructure.Chapter6.ch6DataManagement77 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_Fp/* FormStructure.Chapter6.ch6DataManagement18 */),
_Fu/* ch6DataManagement4 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_Fv/* ch6DataManagement16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total cost of data management"));
}),
_Fw/* ch6DataManagement15 */ = new T1(1,_Fv/* FormStructure.Chapter6.ch6DataManagement16 */),
_Fx/* ch6DataManagement14 */ = {_:0,a:_Fw/* FormStructure.Chapter6.ch6DataManagement15 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Fy/* ch6DataManagement12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_Fz/* ch6DataManagement11 */ = new T1(1,_Fy/* FormStructure.Chapter6.ch6DataManagement12 */),
_FA/* ch6DataManagement10 */ = {_:0,a:_Fz/* FormStructure.Chapter6.ch6DataManagement11 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FB/* ch6DataManagement9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_FC/* ch6DataManagement8 */ = new T1(0,_FB/* FormStructure.Chapter6.ch6DataManagement9 */),
_FD/* ch6DataManagement7 */ = new T2(3,_FA/* FormStructure.Chapter6.ch6DataManagement10 */,_FC/* FormStructure.Chapter6.ch6DataManagement8 */),
_FE/* ch6DataManagement6 */ = new T2(1,_FD/* FormStructure.Chapter6.ch6DataManagement7 */,_I/* GHC.Types.[] */),
_FF/* ch6DataManagement5 */ = new T3(8,_Fx/* FormStructure.Chapter6.ch6DataManagement14 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_FE/* FormStructure.Chapter6.ch6DataManagement6 */),
_FG/* ch6DataManagement3 */ = new T2(1,_FF/* FormStructure.Chapter6.ch6DataManagement5 */,_Fu/* FormStructure.Chapter6.ch6DataManagement4 */),
_FH/* ch6DataManagement2 */ = new T2(1,_Ft/* FormStructure.Chapter6.ch6DataManagement17 */,_FG/* FormStructure.Chapter6.ch6DataManagement3 */),
_FI/* ch6DataManagement86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("community use"));
}),
_FJ/* ch6DataManagement85 */ = new T1(1,_FI/* FormStructure.Chapter6.ch6DataManagement86 */),
_FK/* ch6DataManagement84 */ = {_:0,a:_FJ/* FormStructure.Chapter6.ch6DataManagement85 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FL/* ch6DataManagement83 */ = new T3(9,_FK/* FormStructure.Chapter6.ch6DataManagement84 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_FM/* ch6DataManagement82 */ = new T2(1,_FL/* FormStructure.Chapter6.ch6DataManagement83 */,_I/* GHC.Types.[] */),
_FN/* ch6DataManagement90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("local use"));
}),
_FO/* ch6DataManagement89 */ = new T1(1,_FN/* FormStructure.Chapter6.ch6DataManagement90 */),
_FP/* ch6DataManagement88 */ = {_:0,a:_FO/* FormStructure.Chapter6.ch6DataManagement89 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FQ/* ch6DataManagement87 */ = new T3(9,_FP/* FormStructure.Chapter6.ch6DataManagement88 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_FR/* ch6DataManagement81 */ = new T2(1,_FQ/* FormStructure.Chapter6.ch6DataManagement87 */,_FM/* FormStructure.Chapter6.ch6DataManagement82 */),
_FS/* ch6DataManagement93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We perform data management for:"));
}),
_FT/* ch6DataManagement92 */ = new T1(1,_FS/* FormStructure.Chapter6.ch6DataManagement93 */),
_FU/* ch6DataManagement91 */ = {_:0,a:_FT/* FormStructure.Chapter6.ch6DataManagement92 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FV/* ch6DataManagement80 */ = new T3(8,_FU/* FormStructure.Chapter6.ch6DataManagement91 */,_Eo/* FormStructure.Chapter6.ch6DataManagement13 */,_FR/* FormStructure.Chapter6.ch6DataManagement81 */),
_FW/* ch6DataManagement1 */ = new T2(1,_FV/* FormStructure.Chapter6.ch6DataManagement80 */,_FH/* FormStructure.Chapter6.ch6DataManagement2 */),
_FX/* ch6DataManagement96 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("6.Management "));
}),
_FY/* ch6DataManagement95 */ = new T1(1,_FX/* FormStructure.Chapter6.ch6DataManagement96 */),
_FZ/* ch6DataManagement94 */ = {_:0,a:_FY/* FormStructure.Chapter6.ch6DataManagement95 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_G0/* ch6DataManagement */ = new T2(7,_FZ/* FormStructure.Chapter6.ch6DataManagement94 */,_FW/* FormStructure.Chapter6.ch6DataManagement1 */),
_G1/* ch7Roles2 */ = new T2(1,_8r/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_G2/* ch7Roles13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Full-time equivalent"));
}),
_G3/* ch7Roles12 */ = new T1(0,_G2/* FormStructure.Chapter7.ch7Roles13 */),
_G4/* ch7Roles16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haste[\'toRoles\']()"));
}),
_G5/* ch7Roles15 */ = new T1(1,_G4/* FormStructure.Chapter7.ch7Roles16 */),
_G6/* ch7Roles27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_G7/* ch7Roles36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_G8/* ch7Roles26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_G9/* ch7Roles59 */ = new T2(1,_G8/* FormStructure.Chapter7.ch7Roles26 */,_I/* GHC.Types.[] */),
_Ga/* ch7Roles58 */ = new T2(1,_G7/* FormStructure.Chapter7.ch7Roles36 */,_G9/* FormStructure.Chapter7.ch7Roles59 */),
_Gb/* ch7Roles57 */ = new T2(1,_G6/* FormStructure.Chapter7.ch7Roles27 */,_Ga/* FormStructure.Chapter7.ch7Roles58 */),
_Gc/* ch7Roles61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data expert"));
}),
_Gd/* ch7Roles60 */ = new T1(1,_Gc/* FormStructure.Chapter7.ch7Roles61 */),
_Ge/* ch7Roles56 */ = {_:0,a:_Gd/* FormStructure.Chapter7.ch7Roles60 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Gb/* FormStructure.Chapter7.ch7Roles57 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gf/* ch7Roles55 */ = new T2(3,_Ge/* FormStructure.Chapter7.ch7Roles56 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_Gg/* ch7Roles52 */ = new T2(1,_G7/* FormStructure.Chapter7.ch7Roles36 */,_I/* GHC.Types.[] */),
_Gh/* ch7Roles54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data consumer"));
}),
_Gi/* ch7Roles53 */ = new T1(1,_Gh/* FormStructure.Chapter7.ch7Roles54 */),
_Gj/* ch7Roles51 */ = {_:0,a:_Gi/* FormStructure.Chapter7.ch7Roles53 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Gg/* FormStructure.Chapter7.ch7Roles52 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gk/* ch7Roles50 */ = new T2(3,_Gj/* FormStructure.Chapter7.ch7Roles51 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_Gl/* ch7Roles23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_Gm/* ch7Roles22 */ = new T2(1,_Gl/* FormStructure.Chapter7.ch7Roles23 */,_I/* GHC.Types.[] */),
_Gn/* ch7Roles24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_Go/* ch7Roles21 */ = new T2(1,_Gn/* FormStructure.Chapter7.ch7Roles24 */,_Gm/* FormStructure.Chapter7.ch7Roles22 */),
_Gp/* ch7Roles25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_Gq/* ch7Roles20 */ = new T2(1,_Gp/* FormStructure.Chapter7.ch7Roles25 */,_Go/* FormStructure.Chapter7.ch7Roles21 */),
_Gr/* ch7Roles19 */ = new T2(1,_G8/* FormStructure.Chapter7.ch7Roles26 */,_Gq/* FormStructure.Chapter7.ch7Roles20 */),
_Gs/* ch7Roles35 */ = new T2(1,_G7/* FormStructure.Chapter7.ch7Roles36 */,_Gr/* FormStructure.Chapter7.ch7Roles19 */),
_Gt/* ch7Roles34 */ = new T2(1,_G6/* FormStructure.Chapter7.ch7Roles27 */,_Gs/* FormStructure.Chapter7.ch7Roles35 */),
_Gu/* ch7Roles49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data curator"));
}),
_Gv/* ch7Roles48 */ = new T1(1,_Gu/* FormStructure.Chapter7.ch7Roles49 */),
_Gw/* ch7Roles47 */ = {_:0,a:_Gv/* FormStructure.Chapter7.ch7Roles48 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Gt/* FormStructure.Chapter7.ch7Roles34 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gx/* ch7Roles46 */ = new T2(3,_Gw/* FormStructure.Chapter7.ch7Roles47 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_Gy/* ch7Roles43 */ = new T2(1,_Gn/* FormStructure.Chapter7.ch7Roles24 */,_I/* GHC.Types.[] */),
_Gz/* ch7Roles42 */ = new T2(1,_Gp/* FormStructure.Chapter7.ch7Roles25 */,_Gy/* FormStructure.Chapter7.ch7Roles43 */),
_GA/* ch7Roles41 */ = new T2(1,_G8/* FormStructure.Chapter7.ch7Roles26 */,_Gz/* FormStructure.Chapter7.ch7Roles42 */),
_GB/* ch7Roles45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data custodian"));
}),
_GC/* ch7Roles44 */ = new T1(1,_GB/* FormStructure.Chapter7.ch7Roles45 */),
_GD/* ch7Roles40 */ = {_:0,a:_GC/* FormStructure.Chapter7.ch7Roles44 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GA/* FormStructure.Chapter7.ch7Roles41 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GE/* ch7Roles39 */ = new T2(3,_GD/* FormStructure.Chapter7.ch7Roles40 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_GF/* ch7Roles18 */ = new T2(1,_G6/* FormStructure.Chapter7.ch7Roles27 */,_Gr/* FormStructure.Chapter7.ch7Roles19 */),
_GG/* ch7Roles28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_GH/* ch7Roles17 */ = new T2(1,_GG/* FormStructure.Chapter7.ch7Roles28 */,_GF/* FormStructure.Chapter7.ch7Roles18 */),
_GI/* ch7Roles30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data manager"));
}),
_GJ/* ch7Roles29 */ = new T1(1,_GI/* FormStructure.Chapter7.ch7Roles30 */),
_GK/* ch7Roles14 */ = {_:0,a:_GJ/* FormStructure.Chapter7.ch7Roles29 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GH/* FormStructure.Chapter7.ch7Roles17 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GL/* ch7Roles11 */ = new T2(3,_GK/* FormStructure.Chapter7.ch7Roles14 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_GM/* ch7Roles10 */ = new T2(1,_GL/* FormStructure.Chapter7.ch7Roles11 */,_I/* GHC.Types.[] */),
_GN/* ch7Roles33 */ = new T2(1,_GG/* FormStructure.Chapter7.ch7Roles28 */,_Gt/* FormStructure.Chapter7.ch7Roles34 */),
_GO/* ch7Roles38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data steward"));
}),
_GP/* ch7Roles37 */ = new T1(1,_GO/* FormStructure.Chapter7.ch7Roles38 */),
_GQ/* ch7Roles32 */ = {_:0,a:_GP/* FormStructure.Chapter7.ch7Roles37 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GN/* FormStructure.Chapter7.ch7Roles33 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GR/* ch7Roles31 */ = new T2(3,_GQ/* FormStructure.Chapter7.ch7Roles32 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_GS/* ch7Roles9 */ = new T2(1,_GR/* FormStructure.Chapter7.ch7Roles31 */,_GM/* FormStructure.Chapter7.ch7Roles10 */),
_GT/* ch7Roles8 */ = new T2(1,_GE/* FormStructure.Chapter7.ch7Roles39 */,_GS/* FormStructure.Chapter7.ch7Roles9 */),
_GU/* ch7Roles7 */ = new T2(1,_Gx/* FormStructure.Chapter7.ch7Roles46 */,_GT/* FormStructure.Chapter7.ch7Roles8 */),
_GV/* ch7Roles6 */ = new T2(1,_Gk/* FormStructure.Chapter7.ch7Roles50 */,_GU/* FormStructure.Chapter7.ch7Roles7 */),
_GW/* ch7Roles5 */ = new T2(1,_Gf/* FormStructure.Chapter7.ch7Roles55 */,_GV/* FormStructure.Chapter7.ch7Roles6 */),
_GX/* ch7Roles64 */ = new T2(1,_GG/* FormStructure.Chapter7.ch7Roles28 */,_I/* GHC.Types.[] */),
_GY/* ch7Roles66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data producer"));
}),
_GZ/* ch7Roles65 */ = new T1(1,_GY/* FormStructure.Chapter7.ch7Roles66 */),
_H0/* ch7Roles63 */ = {_:0,a:_GZ/* FormStructure.Chapter7.ch7Roles65 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GX/* FormStructure.Chapter7.ch7Roles64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_G5/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_H1/* ch7Roles62 */ = new T2(3,_H0/* FormStructure.Chapter7.ch7Roles63 */,_G3/* FormStructure.Chapter7.ch7Roles12 */),
_H2/* ch7Roles4 */ = new T2(1,_H1/* FormStructure.Chapter7.ch7Roles62 */,_GW/* FormStructure.Chapter7.ch7Roles5 */),
_H3/* ch7Roles67 */ = 0,
_H4/* ch7Roles70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Employed roles"));
}),
_H5/* ch7Roles69 */ = new T1(1,_H4/* FormStructure.Chapter7.ch7Roles70 */),
_H6/* ch7Roles68 */ = {_:0,a:_H5/* FormStructure.Chapter7.ch7Roles69 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_H7/* ch7Roles3 */ = new T3(8,_H6/* FormStructure.Chapter7.ch7Roles68 */,_H3/* FormStructure.Chapter7.ch7Roles67 */,_H2/* FormStructure.Chapter7.ch7Roles4 */),
_H8/* ch7Roles1 */ = new T2(1,_H7/* FormStructure.Chapter7.ch7Roles3 */,_G1/* FormStructure.Chapter7.ch7Roles2 */),
_H9/* ch7Roles73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("7.Roles "));
}),
_Ha/* ch7Roles72 */ = new T1(1,_H9/* FormStructure.Chapter7.ch7Roles73 */),
_Hb/* ch7Roles71 */ = {_:0,a:_Ha/* FormStructure.Chapter7.ch7Roles72 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Hc/* ch7Roles */ = new T2(7,_Hb/* FormStructure.Chapter7.ch7Roles71 */,_H8/* FormStructure.Chapter7.ch7Roles1 */),
_Hd/* submitForm5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save your answers."));
}),
_He/* submitForm4 */ = new T1(1,_Hd/* FormStructure.Submit.submitForm5 */),
_Hf/* submitForm3 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_He/* FormStructure.Submit.submitForm4 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8n/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Hg/* submitForm2 */ = new T1(11,_Hf/* FormStructure.Submit.submitForm3 */),
_Hh/* submitForm1 */ = new T2(1,_Hg/* FormStructure.Submit.submitForm2 */,_I/* GHC.Types.[] */),
_Hi/* submitForm8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finish"));
}),
_Hj/* submitForm7 */ = new T1(1,_Hi/* FormStructure.Submit.submitForm8 */),
_Hk/* submitForm6 */ = {_:0,a:_Hj/* FormStructure.Submit.submitForm7 */,b:_8g/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Hl/* submitForm */ = new T2(7,_Hk/* FormStructure.Submit.submitForm6 */,_Hh/* FormStructure.Submit.submitForm1 */),
_Hm/* formItems9 */ = new T2(1,_Hl/* FormStructure.Submit.submitForm */,_I/* GHC.Types.[] */),
_Hn/* formItems8 */ = new T2(1,_Hc/* FormStructure.Chapter7.ch7Roles */,_Hm/* FormStructure.FormStructure.formItems9 */),
_Ho/* formItems7 */ = new T2(1,_G0/* FormStructure.Chapter6.ch6DataManagement */,_Hn/* FormStructure.FormStructure.formItems8 */),
_Hp/* formItems6 */ = new T2(1,_En/* FormStructure.Chapter5.ch5DataAccessibility */,_Ho/* FormStructure.FormStructure.formItems7 */),
_Hq/* formItems5 */ = new T2(1,_DN/* FormStructure.Chapter4.ch4DataStorage */,_Hp/* FormStructure.FormStructure.formItems6 */),
_Hr/* formItems4 */ = new T2(1,_Ck/* FormStructure.Chapter3.ch3DataUsage */,_Hq/* FormStructure.FormStructure.formItems5 */),
_Hs/* formItems3 */ = new T2(1,_xT/* FormStructure.Chapter2.ch2DataProcessing */,_Hr/* FormStructure.FormStructure.formItems4 */),
_Ht/* formItems2 */ = new T2(1,_tB/* FormStructure.Chapter1.ch1DataProduction */,_Hs/* FormStructure.FormStructure.formItems3 */),
_Hu/* formItems1 */ = new T2(1,_pz/* FormStructure.Chapter0.ch0GeneralInformation */,_Ht/* FormStructure.FormStructure.formItems2 */),
_Hv/* prepareForm_xs */ = new T(function(){
  return new T2(1,_5U/* FormEngine.FormItem.$fShowNumbering2 */,_Hv/* FormEngine.FormItem.prepareForm_xs */);
}),
_Hw/* prepareForm1 */ = new T2(1,_Hv/* FormEngine.FormItem.prepareForm_xs */,_5U/* FormEngine.FormItem.$fShowNumbering2 */),
_Hx/* formItems */ = new T(function(){
  return E(B(_85/* FormEngine.FormItem.$wgo1 */(_Hu/* FormStructure.FormStructure.formItems1 */, _Hw/* FormEngine.FormItem.prepareForm1 */, _I/* GHC.Types.[] */)).b);
}),
_Hy/* $fHasChildrenFormElement_go */ = function(_Hz/* s6HY */){
  var _HA/* s6HZ */ = E(_Hz/* s6HY */);
  if(!_HA/* s6HZ */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _12/* GHC.Base.++ */(E(_HA/* s6HZ */.a).a, new T(function(){
      return B(_Hy/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_HA/* s6HZ */.b));
    },1));});
  }
},
_HB/* $fHasChildrenFormElement_go1 */ = function(_HC/*  s6HL */, _HD/*  s6HM */){
  while(1){
    var _HE/*  $fHasChildrenFormElement_go1 */ = B((function(_HF/* s6HL */, _HG/* s6HM */){
      var _HH/* s6HN */ = E(_HF/* s6HL */);
      if(!_HH/* s6HN */._){
        return E(_HG/* s6HM */);
      }else{
        var _HI/*   s6HM */ = B(_12/* GHC.Base.++ */(_HG/* s6HM */, new T(function(){
          var _HJ/* s6HQ */ = E(_HH/* s6HN */.a);
          if(!_HJ/* s6HQ */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_HJ/* s6HQ */.c);
          }
        },1)));
        _HC/*  s6HL */ = _HH/* s6HN */.b;
        _HD/*  s6HM */ = _HI/*   s6HM */;
        return __continue/* EXTERNAL */;
      }
    })(_HC/*  s6HL */, _HD/*  s6HM */));
    if(_HE/*  $fHasChildrenFormElement_go1 */!=__continue/* EXTERNAL */){
      return _HE/*  $fHasChildrenFormElement_go1 */;
    }
  }
},
_HK/* $fHasChildrenFormElement_$cchildren */ = function(_HL/* s6I6 */){
  var _HM/* s6I7 */ = E(_HL/* s6I6 */);
  switch(_HM/* s6I7 */._){
    case 0:
      return E(_HM/* s6I7 */.b);
    case 6:
      return new F(function(){return _HB/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go1 */(_HM/* s6I7 */.b, _I/* GHC.Types.[] */);});
      break;
    case 8:
      return E(_HM/* s6I7 */.b);
    case 9:
      return E(_HM/* s6I7 */.c);
    case 10:
      return new F(function(){return _Hy/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_HM/* s6I7 */.b);});
      break;
    default:
      return __Z/* EXTERNAL */;
  }
},
_HN/* addClass2 */ = "(function (cls, jq) { jq.addClass(cls); return jq; })",
_HO/* $wa */ = function(_HP/* stTb */, _HQ/* stTc */, _/* EXTERNAL */){
  var _HR/* stTm */ = eval/* EXTERNAL */(E(_HN/* FormEngine.JQuery.addClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_HR/* stTm */), toJSStr/* EXTERNAL */(E(_HP/* stTb */)), _HQ/* stTc */);});
},
_HS/* disableJq5 */ = "(function (k, v, jq) { jq.attr(k, v); return jq; })",
_HT/* $wa6 */ = function(_HU/* stUq */, _HV/* stUr */, _HW/* stUs */, _/* EXTERNAL */){
  var _HX/* stUH */ = eval/* EXTERNAL */(E(_HS/* FormEngine.JQuery.disableJq5 */));
  return new F(function(){return __app3/* EXTERNAL */(E(_HX/* stUH */), toJSStr/* EXTERNAL */(E(_HU/* stUq */)), toJSStr/* EXTERNAL */(E(_HV/* stUr */)), _HW/* stUs */);});
},
_HY/* addClassInside_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.parent(); })");
}),
_HZ/* addClassInside_f2 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.last(); })");
}),
_I0/* addClassInside_f3 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.children(); })");
}),
_I1/* $wa20 */ = function(_I2/* stUZ */, _I3/* stV0 */, _I4/* stV1 */, _/* EXTERNAL */){
  var _I5/* stV6 */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _I4/* stV1 */),
  _I6/* stVc */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _I5/* stV6 */),
  _I7/* stVf */ = B(_HT/* FormEngine.JQuery.$wa6 */(_I2/* stUZ */, _I3/* stV0 */, _I6/* stVc */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_I7/* stVf */));});
},
_I8/* $wa24 */ = function(_I9/* stWg */, _Ia/* stWh */, _Ib/* stWi */, _/* EXTERNAL */){
  var _Ic/* stWn */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _Ib/* stWi */),
  _Id/* stWt */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _Ic/* stWn */),
  _Ie/* stWw */ = B(_43/* FormEngine.JQuery.$wa2 */(_I9/* stWg */, _Ia/* stWh */, _Id/* stWt */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_Ie/* stWw */));});
},
_If/* appendT2 */ = "(function (tag, jq) { return jq.append(tag); })",
_Ig/* $wa3 */ = function(_Ih/* stSb */, _Ii/* stSc */, _/* EXTERNAL */){
  var _Ij/* stSm */ = eval/* EXTERNAL */(E(_If/* FormEngine.JQuery.appendT2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_Ij/* stSm */), toJSStr/* EXTERNAL */(E(_Ih/* stSb */)), _Ii/* stSc */);});
},
_Ik/* setText2 */ = "(function (txt, jq) { jq.text(txt); return jq; })",
_Il/* $wa34 */ = function(_Im/* stZ3 */, _In/* stZ4 */, _/* EXTERNAL */){
  var _Io/* stZ9 */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _In/* stZ4 */),
  _Ip/* stZf */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _Io/* stZ9 */),
  _Iq/* stZq */ = eval/* EXTERNAL */(E(_Ik/* FormEngine.JQuery.setText2 */)),
  _Ir/* stZy */ = __app2/* EXTERNAL */(E(_Iq/* stZq */), toJSStr/* EXTERNAL */(E(_Im/* stZ3 */)), _Ip/* stZf */);
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), _Ir/* stZy */);});
},
_Is/* appendJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq, toJq) { return toJq.append(jq); })");
}),
_It/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<ul>"));
}),
_Iu/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("nav"));
}),
_Iv/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<li>"));
}),
_Iw/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_Ix/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<a>"));
}),
_Iy/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'stripe stripe-thin\'>"));
}),
_Iz/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_IA/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_IB/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("class"));
}),
_IC/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inside-bordered"));
}),
_ID/* onClick2 */ = "(function (ev, jq) { jq.click(ev); })",
_IE/* onClick1 */ = function(_IF/* stxG */, _IG/* stxH */, _/* EXTERNAL */){
  var _IH/* stxT */ = __createJSFunc/* EXTERNAL */(2, function(_II/* stxK */, _/* EXTERNAL */){
    var _IJ/* stxM */ = B(A2(E(_IF/* stxG */),_II/* stxK */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _IK/* stxW */ = E(_IG/* stxH */),
  _IL/* sty1 */ = eval/* EXTERNAL */(E(_ID/* FormEngine.JQuery.onClick2 */)),
  _IM/* sty9 */ = __app2/* EXTERNAL */(E(_IL/* sty1 */), _IH/* stxT */, _IK/* stxW */);
  return _IK/* stxW */;
},
_IN/* paneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pane_"));
}),
_IO/* paneId */ = function(_IP/* sc7R */){
  return new F(function(){return _12/* GHC.Base.++ */(_IN/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
    return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_IP/* sc7R */));
  },1));});
},
_IQ/* tabId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tab_"));
}),
_IR/* tabId */ = function(_IS/* sc7T */){
  return new F(function(){return _12/* GHC.Base.++ */(_IQ/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
    return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_IS/* sc7T */));
  },1));});
},
_IT/* tabName */ = function(_IU/* sc6J */){
  var _IV/* sc6V */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_IU/* sc6J */)))).a);
  return (_IV/* sc6V */._==0) ? __Z/* EXTERNAL */ : E(_IV/* sc6V */.a);
},
_IW/* appearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("block"));
}),
_IX/* appearJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_IY/* removeClass2 */ = "(function (cls, jq) { jq.removeClass(cls); return jq; })",
_IZ/* $wa16 */ = function(_J0/* stSG */, _J1/* stSH */, _/* EXTERNAL */){
  var _J2/* stSR */ = eval/* EXTERNAL */(E(_IY/* FormEngine.JQuery.removeClass2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_J2/* stSR */), toJSStr/* EXTERNAL */(E(_J0/* stSG */)), _J1/* stSH */);});
},
_J3/* colorizeTabs2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("notcurrent"));
}),
_J4/* colorizeTabs3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("current"));
}),
_J5/* colorizeTabs5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_J6/* colorizeTabs4 */ = function(_J7/* sdnc */, _/* EXTERNAL */){
  var _J8/* sdnf */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_IQ/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
      return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_J7/* sdnc */));
    },1)));
  },1);
  return new F(function(){return _56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J5/* FormEngine.FormElement.Tabs.colorizeTabs5 */, _J8/* sdnf */)), _/* EXTERNAL */);});
},
_J9/* eqString */ = function(_Ja/* s3mQ */, _Jb/* s3mR */){
  while(1){
    var _Jc/* s3mS */ = E(_Ja/* s3mQ */);
    if(!_Jc/* s3mS */._){
      return (E(_Jb/* s3mR */)._==0) ? true : false;
    }else{
      var _Jd/* s3mY */ = E(_Jb/* s3mR */);
      if(!_Jd/* s3mY */._){
        return false;
      }else{
        if(E(_Jc/* s3mS */.a)!=E(_Jd/* s3mY */.a)){
          return false;
        }else{
          _Ja/* s3mQ */ = _Jc/* s3mS */.b;
          _Jb/* s3mR */ = _Jd/* s3mY */.b;
          continue;
        }
      }
    }
  }
},
_Je/* colorizeTabs1 */ = function(_Jf/* sdnt */, _Jg/* sdnu */, _/* EXTERNAL */){
  var _Jh/* sdnw */ = new T(function(){
    return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_Jf/* sdnt */));
  }),
  _Ji/* sdnx */ = function(_Jj/* sdny */, _/* EXTERNAL */){
    while(1){
      var _Jk/* sdnA */ = E(_Jj/* sdny */);
      if(!_Jk/* sdnA */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _Jl/* sdnB */ = _Jk/* sdnA */.a,
        _Jm/* sdnC */ = _Jk/* sdnA */.b;
        if(!B(_J9/* GHC.Base.eqString */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_Jl/* sdnB */)), _Jh/* sdnw */))){
          var _Jn/* sdnF */ = B(_J6/* FormEngine.FormElement.Tabs.colorizeTabs4 */(_Jl/* sdnB */, _/* EXTERNAL */)),
          _Jo/* sdnK */ = B(_IZ/* FormEngine.JQuery.$wa16 */(_J4/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_Jn/* sdnF */), _/* EXTERNAL */)),
          _Jp/* sdnP */ = B(_HO/* FormEngine.JQuery.$wa */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_Jo/* sdnK */), _/* EXTERNAL */));
          _Jj/* sdny */ = _Jm/* sdnC */;
          continue;
        }else{
          var _Jq/* sdnS */ = B(_J6/* FormEngine.FormElement.Tabs.colorizeTabs4 */(_Jl/* sdnB */, _/* EXTERNAL */)),
          _Jr/* sdnX */ = B(_IZ/* FormEngine.JQuery.$wa16 */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_Jq/* sdnS */), _/* EXTERNAL */)),
          _Js/* sdo2 */ = B(_HO/* FormEngine.JQuery.$wa */(_J4/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_Jr/* sdnX */), _/* EXTERNAL */));
          _Jj/* sdny */ = _Jm/* sdnC */;
          continue;
        }
      }
    }
  };
  return new F(function(){return _Ji/* sdnx */(_Jg/* sdnu */, _/* EXTERNAL */);});
},
_Jt/* disappearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_Ju/* toTab2 */ = function(_Jv/* sdom */, _/* EXTERNAL */){
  while(1){
    var _Jw/* sdoo */ = E(_Jv/* sdom */);
    if(!_Jw/* sdoo */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _Jx/* sdot */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, E(_Jw/* sdoo */.a), _/* EXTERNAL */));
      _Jv/* sdom */ = _Jw/* sdoo */.b;
      continue;
    }
  }
},
_Jy/* toTab4 */ = function(_Jz/* sdo5 */, _/* EXTERNAL */){
  var _JA/* sdo8 */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_IN/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
      return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_Jz/* sdo5 */));
    },1)));
  },1);
  return new F(function(){return _56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J5/* FormEngine.FormElement.Tabs.colorizeTabs5 */, _JA/* sdo8 */)), _/* EXTERNAL */);});
},
_JB/* toTab3 */ = function(_JC/* sdoa */, _/* EXTERNAL */){
  var _JD/* sdoc */ = E(_JC/* sdoa */);
  if(!_JD/* sdoc */._){
    return _I/* GHC.Types.[] */;
  }else{
    var _JE/* sdof */ = B(_Jy/* FormEngine.FormElement.Tabs.toTab4 */(_JD/* sdoc */.a, _/* EXTERNAL */)),
    _JF/* sdoi */ = B(_JB/* FormEngine.FormElement.Tabs.toTab3 */(_JD/* sdoc */.b, _/* EXTERNAL */));
    return new T2(1,_JE/* sdof */,_JF/* sdoi */);
  }
},
_JG/* toTab1 */ = function(_JH/* sdow */, _JI/* sdox */, _/* EXTERNAL */){
  var _JJ/* sdoz */ = B(_Jy/* FormEngine.FormElement.Tabs.toTab4 */(_JH/* sdow */, _/* EXTERNAL */)),
  _JK/* sdoC */ = B(_JB/* FormEngine.FormElement.Tabs.toTab3 */(_JI/* sdox */, _/* EXTERNAL */)),
  _JL/* sdoF */ = B(_Je/* FormEngine.FormElement.Tabs.colorizeTabs1 */(_JH/* sdow */, _JI/* sdox */, _/* EXTERNAL */)),
  _JM/* sdoI */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab2 */(_JK/* sdoC */, _/* EXTERNAL */)),
  _JN/* sdoN */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _IW/* FormEngine.JQuery.appearJq2 */, E(_JJ/* sdoz */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_JO/* $wa */ = function(_JP/* sdoQ */, _JQ/* sdoR */, _JR/* sdoS */, _/* EXTERNAL */){
  var _JS/* sdoU */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_It/* FormEngine.FormElement.Tabs.lvl */, _JR/* sdoS */, _/* EXTERNAL */)),
  _JT/* sdoZ */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
  _JU/* sdp2 */ = __app1/* EXTERNAL */(_JT/* sdoZ */, E(_JS/* sdoU */)),
  _JV/* sdp5 */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
  _JW/* sdp8 */ = __app1/* EXTERNAL */(_JV/* sdp5 */, _JU/* sdp2 */),
  _JX/* sdpb */ = B(_HO/* FormEngine.JQuery.$wa */(_Iu/* FormEngine.FormElement.Tabs.lvl1 */, _JW/* sdp8 */, _/* EXTERNAL */)),
  _JY/* sdpe */ = function(_/* EXTERNAL */, _JZ/* sdpg */){
    var _K0/* sdpm */ = __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_JZ/* sdpg */)),
    _K1/* sdpp */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_Iy/* FormEngine.FormElement.Tabs.lvl5 */, _K0/* sdpm */, _/* EXTERNAL */)),
    _K2/* sdps */ = E(_JP/* sdoQ */);
    if(!_K2/* sdps */._){
      return _K1/* sdpp */;
    }else{
      var _K3/* sdpv */ = E(_JQ/* sdoR */);
      if(!_K3/* sdpv */._){
        return _K1/* sdpp */;
      }else{
        var _K4/* sdpy */ = B(A1(_K3/* sdpv */.a,_/* EXTERNAL */)),
        _K5/* sdpF */ = E(_Is/* FormEngine.JQuery.appendJq_f1 */),
        _K6/* sdpI */ = __app2/* EXTERNAL */(_K5/* sdpF */, E(_K4/* sdpy */), E(_K1/* sdpp */)),
        _K7/* sdpM */ = B(_I1/* FormEngine.JQuery.$wa20 */(_Iw/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
          return B(_IO/* FormEngine.FormElement.Identifiers.paneId */(_K2/* sdps */.a));
        },1), _K6/* sdpI */, _/* EXTERNAL */)),
        _K8/* sdpR */ = B(_I8/* FormEngine.JQuery.$wa24 */(_Iz/* FormEngine.FormElement.Tabs.lvl6 */, _IA/* FormEngine.FormElement.Tabs.lvl7 */, E(_K7/* sdpM */), _/* EXTERNAL */)),
        _K9/* sdpW */ = B(_I1/* FormEngine.JQuery.$wa20 */(_IB/* FormEngine.FormElement.Tabs.lvl8 */, _IC/* FormEngine.FormElement.Tabs.lvl9 */, E(_K8/* sdpR */), _/* EXTERNAL */)),
        _Ka/* sdpZ */ = function(_Kb/*  sdq0 */, _Kc/*  sdq1 */, _Kd/*  sdq2 */, _/* EXTERNAL */){
          while(1){
            var _Ke/*  sdpZ */ = B((function(_Kf/* sdq0 */, _Kg/* sdq1 */, _Kh/* sdq2 */, _/* EXTERNAL */){
              var _Ki/* sdq4 */ = E(_Kf/* sdq0 */);
              if(!_Ki/* sdq4 */._){
                return _Kh/* sdq2 */;
              }else{
                var _Kj/* sdq7 */ = E(_Kg/* sdq1 */);
                if(!_Kj/* sdq7 */._){
                  return _Kh/* sdq2 */;
                }else{
                  var _Kk/* sdqa */ = B(A1(_Kj/* sdq7 */.a,_/* EXTERNAL */)),
                  _Kl/* sdqi */ = __app2/* EXTERNAL */(_K5/* sdpF */, E(_Kk/* sdqa */), E(_Kh/* sdq2 */)),
                  _Km/* sdqm */ = B(_I1/* FormEngine.JQuery.$wa20 */(_Iw/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
                    return B(_IO/* FormEngine.FormElement.Identifiers.paneId */(_Ki/* sdq4 */.a));
                  },1), _Kl/* sdqi */, _/* EXTERNAL */)),
                  _Kn/* sdqr */ = B(_I8/* FormEngine.JQuery.$wa24 */(_Iz/* FormEngine.FormElement.Tabs.lvl6 */, _IA/* FormEngine.FormElement.Tabs.lvl7 */, E(_Km/* sdqm */), _/* EXTERNAL */)),
                  _Ko/* sdqw */ = B(_I1/* FormEngine.JQuery.$wa20 */(_IB/* FormEngine.FormElement.Tabs.lvl8 */, _IC/* FormEngine.FormElement.Tabs.lvl9 */, E(_Kn/* sdqr */), _/* EXTERNAL */));
                  _Kb/*  sdq0 */ = _Ki/* sdq4 */.b;
                  _Kc/*  sdq1 */ = _Kj/* sdq7 */.b;
                  _Kd/*  sdq2 */ = _Ko/* sdqw */;
                  return __continue/* EXTERNAL */;
                }
              }
            })(_Kb/*  sdq0 */, _Kc/*  sdq1 */, _Kd/*  sdq2 */, _/* EXTERNAL */));
            if(_Ke/*  sdpZ */!=__continue/* EXTERNAL */){
              return _Ke/*  sdpZ */;
            }
          }
        };
        return new F(function(){return _Ka/* sdpZ */(_K2/* sdps */.b, _K3/* sdpv */.b, _K9/* sdpW */, _/* EXTERNAL */);});
      }
    }
  },
  _Kp/* sdqz */ = E(_JP/* sdoQ */);
  if(!_Kp/* sdqz */._){
    return new F(function(){return _JY/* sdpe */(_/* EXTERNAL */, _JX/* sdpb */);});
  }else{
    var _Kq/* sdqA */ = _Kp/* sdqz */.a,
    _Kr/* sdqE */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_Iv/* FormEngine.FormElement.Tabs.lvl2 */, E(_JX/* sdpb */), _/* EXTERNAL */)),
    _Ks/* sdqK */ = B(_I1/* FormEngine.JQuery.$wa20 */(_Iw/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
      return B(_IR/* FormEngine.FormElement.Identifiers.tabId */(_Kq/* sdqA */));
    },1), E(_Kr/* sdqE */), _/* EXTERNAL */)),
    _Kt/* sdqQ */ = __app1/* EXTERNAL */(_JT/* sdoZ */, E(_Ks/* sdqK */)),
    _Ku/* sdqU */ = __app1/* EXTERNAL */(_JV/* sdp5 */, _Kt/* sdqQ */),
    _Kv/* sdqX */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_Ix/* FormEngine.FormElement.Tabs.lvl4 */, _Ku/* sdqU */, _/* EXTERNAL */)),
    _Kw/* sdr3 */ = B(_IE/* FormEngine.JQuery.onClick1 */(function(_Kx/* sdr0 */, _/* EXTERNAL */){
      return new F(function(){return _JG/* FormEngine.FormElement.Tabs.toTab1 */(_Kq/* sdqA */, _Kp/* sdqz */, _/* EXTERNAL */);});
    }, _Kv/* sdqX */, _/* EXTERNAL */)),
    _Ky/* sdr9 */ = B(_Il/* FormEngine.JQuery.$wa34 */(new T(function(){
      return B(_IT/* FormEngine.FormElement.Identifiers.tabName */(_Kq/* sdqA */));
    },1), E(_Kw/* sdr3 */), _/* EXTERNAL */)),
    _Kz/* sdre */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
    _KA/* sdrh */ = __app1/* EXTERNAL */(_Kz/* sdre */, E(_Ky/* sdr9 */)),
    _KB/* sdrk */ = function(_KC/*  sdrl */, _KD/*  sdrm */, _KE/*  sdjd */, _/* EXTERNAL */){
      while(1){
        var _KF/*  sdrk */ = B((function(_KG/* sdrl */, _KH/* sdrm */, _KI/* sdjd */, _/* EXTERNAL */){
          var _KJ/* sdro */ = E(_KG/* sdrl */);
          if(!_KJ/* sdro */._){
            return _KH/* sdrm */;
          }else{
            var _KK/* sdrq */ = _KJ/* sdro */.a,
            _KL/* sdrs */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_Iv/* FormEngine.FormElement.Tabs.lvl2 */, _KH/* sdrm */, _/* EXTERNAL */)),
            _KM/* sdry */ = B(_I1/* FormEngine.JQuery.$wa20 */(_Iw/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
              return B(_IR/* FormEngine.FormElement.Identifiers.tabId */(_KK/* sdrq */));
            },1), E(_KL/* sdrs */), _/* EXTERNAL */)),
            _KN/* sdrE */ = __app1/* EXTERNAL */(_JT/* sdoZ */, E(_KM/* sdry */)),
            _KO/* sdrI */ = __app1/* EXTERNAL */(_JV/* sdp5 */, _KN/* sdrE */),
            _KP/* sdrL */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_Ix/* FormEngine.FormElement.Tabs.lvl4 */, _KO/* sdrI */, _/* EXTERNAL */)),
            _KQ/* sdrR */ = B(_IE/* FormEngine.JQuery.onClick1 */(function(_KR/* sdrO */, _/* EXTERNAL */){
              return new F(function(){return _JG/* FormEngine.FormElement.Tabs.toTab1 */(_KK/* sdrq */, _Kp/* sdqz */, _/* EXTERNAL */);});
            }, _KP/* sdrL */, _/* EXTERNAL */)),
            _KS/* sdrX */ = B(_Il/* FormEngine.JQuery.$wa34 */(new T(function(){
              return B(_IT/* FormEngine.FormElement.Identifiers.tabName */(_KK/* sdrq */));
            },1), E(_KQ/* sdrR */), _/* EXTERNAL */)),
            _KT/* sds3 */ = __app1/* EXTERNAL */(_Kz/* sdre */, E(_KS/* sdrX */)),
            _KU/*   sdjd */ = _/* EXTERNAL */;
            _KC/*  sdrl */ = _KJ/* sdro */.b;
            _KD/*  sdrm */ = _KT/* sds3 */;
            _KE/*  sdjd */ = _KU/*   sdjd */;
            return __continue/* EXTERNAL */;
          }
        })(_KC/*  sdrl */, _KD/*  sdrm */, _KE/*  sdjd */, _/* EXTERNAL */));
        if(_KF/*  sdrk */!=__continue/* EXTERNAL */){
          return _KF/*  sdrk */;
        }
      }
    },
    _KV/* sds6 */ = B(_KB/* sdrk */(_Kp/* sdqz */.b, _KA/* sdrh */, _/* EXTERNAL */, _/* EXTERNAL */));
    return new F(function(){return _JY/* sdpe */(_/* EXTERNAL */, _KV/* sds6 */);});
  }
},
_KW/* mouseleave2 */ = "(function (jq) { jq.mouseleave(); })",
_KX/* $wa14 */ = function(_KY/* stzn */, _/* EXTERNAL */){
  var _KZ/* stzs */ = eval/* EXTERNAL */(E(_KW/* FormEngine.JQuery.mouseleave2 */)),
  _L0/* stzA */ = __app1/* EXTERNAL */(E(_KZ/* stzs */), _KY/* stzn */);
  return _KY/* stzn */;
},
_L1/* setHtml2 */ = "(function (html, jq) { jq.html(html); return jq; })",
_L2/* $wa26 */ = function(_L3/* stXm */, _L4/* stXn */, _/* EXTERNAL */){
  var _L5/* stXx */ = eval/* EXTERNAL */(E(_L1/* FormEngine.JQuery.setHtml2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_L5/* stXx */), toJSStr/* EXTERNAL */(E(_L3/* stXm */)), _L4/* stXn */);});
},
_L6/* onLoad2 */ = "(function (ev, jq) { jq[0].addEventListener(\'load\', ev); })",
_L7/* onLoad1 */ = function(_L8/* sttl */, _L9/* sttm */, _/* EXTERNAL */){
  var _La/* stty */ = __createJSFunc/* EXTERNAL */(2, function(_Lb/* sttp */, _/* EXTERNAL */){
    var _Lc/* sttr */ = B(A2(E(_L8/* sttl */),_Lb/* sttp */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _Ld/* sttB */ = E(_L9/* sttm */),
  _Le/* sttG */ = eval/* EXTERNAL */(E(_L6/* FormEngine.JQuery.onLoad2 */)),
  _Lf/* sttO */ = __app2/* EXTERNAL */(E(_Le/* sttG */), _La/* stty */, _Ld/* sttB */);
  return _Ld/* sttB */;
},
_Lg/* $wa29 */ = function(_Lh/* stJi */, _Li/* stJj */, _/* EXTERNAL */){
  var _Lj/* stJo */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _Li/* stJj */),
  _Lk/* stJu */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _Lj/* stJo */),
  _Ll/* stJy */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_Lh/* stJi */, _Lk/* stJu */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_Ll/* stJy */));});
},
_Lm/* click2 */ = "(function (jq) { jq.click(); })",
_Ln/* $wa5 */ = function(_Lo/* stAx */, _/* EXTERNAL */){
  var _Lp/* stAC */ = eval/* EXTERNAL */(E(_Lm/* FormEngine.JQuery.click2 */)),
  _Lq/* stAK */ = __app1/* EXTERNAL */(E(_Lp/* stAC */), _Lo/* stAx */);
  return _Lo/* stAx */;
},
_Lr/* aboutTab4 */ = 0,
_Ls/* aboutTab6 */ = 1000,
_Lt/* aboutTab5 */ = new T2(1,_Ls/* Form.aboutTab6 */,_I/* GHC.Types.[] */),
_Lu/* aboutTab3 */ = new T2(1,_Lt/* Form.aboutTab5 */,_Lr/* Form.aboutTab4 */),
_Lv/* aboutTab8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("About"));
}),
_Lw/* aboutTab7 */ = new T1(1,_Lv/* Form.aboutTab8 */),
_Lx/* aboutTab2 */ = {_:0,a:_Lw/* Form.aboutTab7 */,b:_Lu/* Form.aboutTab3 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ly/* aboutTab1 */ = new T2(7,_Lx/* Form.aboutTab2 */,_I/* GHC.Types.[] */),
_Lz/* aboutTab */ = new T3(0,_Ly/* Form.aboutTab1 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_LA/* aboutTabPaneJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("  <div>    <p>      This questionnaire aims to collect managerial information about the bioinformatics data space.    </p>    <p>      <strong>Only data where the respondent is the owner are subject of the questionnaires</strong>, i.e. not data produced as a service.    </p>    <p>      Its completion should take no more than 15 minutes. If you do not know exact answer, provide your best qualified guess.    </p>    <p>      For questions please contact <a href=\'mailto:robert.pergl@fit.cvut.cz\'>robert.pergl@fit.cvut.cz</a>.    </p>    <br>    <p style=\'font-size: 90%; font-style: italic;\'>      Version of this questionnaire: v2.1    </p>  </div> "));
}),
_LB/* aboutTabPaneJq1 */ = function(_/* EXTERNAL */){
  return new F(function(){return _56/* FormEngine.JQuery.select1 */(_LA/* Form.aboutTabPaneJq2 */, _/* EXTERNAL */);});
},
_LC/* descSubpaneId */ = function(_LD/* sc6X */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_LD/* sc6X */)))), _4m/* FormEngine.FormElement.Identifiers.descSubpaneId1 */);});
},
_LE/* descSubpaneParagraphId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane-text"));
}),
_LF/* descSubpaneParagraphId */ = function(_LG/* sc7V */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_LG/* sc7V */)))), _LE/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */);});
},
_LH/* diagramId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("diagram_"));
}),
_LI/* diagramId */ = function(_LJ/* sc7O */){
  return new F(function(){return _12/* GHC.Base.++ */(_LH/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
    return B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_LJ/* sc7O */))));
  },1));});
},
_LK/* $fEqOption_$c== */ = function(_LL/* s5yP */, _LM/* s5yQ */){
  var _LN/* s5yR */ = E(_LL/* s5yP */);
  if(!_LN/* s5yR */._){
    var _LO/* s5yS */ = _LN/* s5yR */.a,
    _LP/* s5yT */ = E(_LM/* s5yQ */);
    if(!_LP/* s5yT */._){
      return new F(function(){return _J9/* GHC.Base.eqString */(_LO/* s5yS */, _LP/* s5yT */.a);});
    }else{
      return new F(function(){return _J9/* GHC.Base.eqString */(_LO/* s5yS */, _LP/* s5yT */.b);});
    }
  }else{
    var _LQ/* s5yZ */ = _LN/* s5yR */.b,
    _LR/* s5z1 */ = E(_LM/* s5yQ */);
    if(!_LR/* s5z1 */._){
      return new F(function(){return _J9/* GHC.Base.eqString */(_LQ/* s5yZ */, _LR/* s5z1 */.a);});
    }else{
      return new F(function(){return _J9/* GHC.Base.eqString */(_LQ/* s5yZ */, _LR/* s5z1 */.b);});
    }
  }
},
_LS/* $fShowFloat_$cshow */ = function(_LT/* s191X */){
  var _LU/* s1921 */ = jsShow/* EXTERNAL */(E(_LT/* s191X */));
  return new F(function(){return fromJSStr/* EXTERNAL */(_LU/* s1921 */);});
},
_LV/* $fShowFormElement1 */ = function(_LW/* s6Is */, _LX/* s6It */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_LY/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_LW/* s6Is */)), _LX/* s6It */);});
},
_LZ/* $fShowMaybe1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just "));
}),
_M0/* $fShowMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_M1/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SubmitButtonElem id="));
}),
_M2/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SaveButtonElem id="));
}),
_M3/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("InfoElem id="));
}),
_M4/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" unit="));
}),
_M5/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumberElem id="));
}),
_M6/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EmailElem id="));
}),
_M7/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TextElem id="));
}),
_M8/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("StringElem id="));
}),
_M9/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChapterElem id="));
}),
_Ma/* shows5 */ = 34,
_Mb/* lvl17 */ = new T2(1,_Ma/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_Mc/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" groupNo="));
}),
_Md/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElem id="));
}),
_Me/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" children: "));
}),
_Mf/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OptionalGroupElem id="));
}),
_Mg/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SimpleGroupElem id="));
}),
_Mh/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" value="));
}),
_Mi/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ListElem id="));
}),
_Mj/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChoiceElem id="));
}),
_Mk/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_Ml/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_Mm/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_Mn/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_Mo/* asciiTab32 */ = new T2(1,_Mn/* GHC.Show.asciiTab33 */,_I/* GHC.Types.[] */),
_Mp/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_Mq/* asciiTab31 */ = new T2(1,_Mp/* GHC.Show.asciiTab34 */,_Mo/* GHC.Show.asciiTab32 */),
_Mr/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_Ms/* asciiTab30 */ = new T2(1,_Mr/* GHC.Show.asciiTab35 */,_Mq/* GHC.Show.asciiTab31 */),
_Mt/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_Mu/* asciiTab29 */ = new T2(1,_Mt/* GHC.Show.asciiTab36 */,_Ms/* GHC.Show.asciiTab30 */),
_Mv/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_Mw/* asciiTab28 */ = new T2(1,_Mv/* GHC.Show.asciiTab37 */,_Mu/* GHC.Show.asciiTab29 */),
_Mx/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_My/* asciiTab27 */ = new T2(1,_Mx/* GHC.Show.asciiTab38 */,_Mw/* GHC.Show.asciiTab28 */),
_Mz/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_MA/* asciiTab26 */ = new T2(1,_Mz/* GHC.Show.asciiTab39 */,_My/* GHC.Show.asciiTab27 */),
_MB/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_MC/* asciiTab25 */ = new T2(1,_MB/* GHC.Show.asciiTab40 */,_MA/* GHC.Show.asciiTab26 */),
_MD/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_ME/* asciiTab24 */ = new T2(1,_MD/* GHC.Show.asciiTab41 */,_MC/* GHC.Show.asciiTab25 */),
_MF/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_MG/* asciiTab23 */ = new T2(1,_MF/* GHC.Show.asciiTab42 */,_ME/* GHC.Show.asciiTab24 */),
_MH/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_MI/* asciiTab22 */ = new T2(1,_MH/* GHC.Show.asciiTab43 */,_MG/* GHC.Show.asciiTab23 */),
_MJ/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_MK/* asciiTab21 */ = new T2(1,_MJ/* GHC.Show.asciiTab44 */,_MI/* GHC.Show.asciiTab22 */),
_ML/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_MM/* asciiTab20 */ = new T2(1,_ML/* GHC.Show.asciiTab45 */,_MK/* GHC.Show.asciiTab21 */),
_MN/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_MO/* asciiTab19 */ = new T2(1,_MN/* GHC.Show.asciiTab46 */,_MM/* GHC.Show.asciiTab20 */),
_MP/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_MQ/* asciiTab18 */ = new T2(1,_MP/* GHC.Show.asciiTab47 */,_MO/* GHC.Show.asciiTab19 */),
_MR/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_MS/* asciiTab17 */ = new T2(1,_MR/* GHC.Show.asciiTab48 */,_MQ/* GHC.Show.asciiTab18 */),
_MT/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_MU/* asciiTab16 */ = new T2(1,_MT/* GHC.Show.asciiTab49 */,_MS/* GHC.Show.asciiTab17 */),
_MV/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_MW/* asciiTab15 */ = new T2(1,_MV/* GHC.Show.asciiTab50 */,_MU/* GHC.Show.asciiTab16 */),
_MX/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_MY/* asciiTab14 */ = new T2(1,_MX/* GHC.Show.asciiTab51 */,_MW/* GHC.Show.asciiTab15 */),
_MZ/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_N0/* asciiTab13 */ = new T2(1,_MZ/* GHC.Show.asciiTab52 */,_MY/* GHC.Show.asciiTab14 */),
_N1/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_N2/* asciiTab12 */ = new T2(1,_N1/* GHC.Show.asciiTab53 */,_N0/* GHC.Show.asciiTab13 */),
_N3/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_N4/* asciiTab11 */ = new T2(1,_N3/* GHC.Show.asciiTab54 */,_N2/* GHC.Show.asciiTab12 */),
_N5/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_N6/* asciiTab10 */ = new T2(1,_N5/* GHC.Show.asciiTab55 */,_N4/* GHC.Show.asciiTab11 */),
_N7/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_N8/* asciiTab9 */ = new T2(1,_N7/* GHC.Show.asciiTab56 */,_N6/* GHC.Show.asciiTab10 */),
_N9/* asciiTab8 */ = new T2(1,_Mm/* GHC.Show.asciiTab57 */,_N8/* GHC.Show.asciiTab9 */),
_Na/* asciiTab7 */ = new T2(1,_Ml/* GHC.Show.asciiTab58 */,_N9/* GHC.Show.asciiTab8 */),
_Nb/* asciiTab6 */ = new T2(1,_Mk/* GHC.Show.asciiTab59 */,_Na/* GHC.Show.asciiTab7 */),
_Nc/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_Nd/* asciiTab5 */ = new T2(1,_Nc/* GHC.Show.asciiTab60 */,_Nb/* GHC.Show.asciiTab6 */),
_Ne/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_Nf/* asciiTab4 */ = new T2(1,_Ne/* GHC.Show.asciiTab61 */,_Nd/* GHC.Show.asciiTab5 */),
_Ng/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_Nh/* asciiTab3 */ = new T2(1,_Ng/* GHC.Show.asciiTab62 */,_Nf/* GHC.Show.asciiTab4 */),
_Ni/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_Nj/* asciiTab2 */ = new T2(1,_Ni/* GHC.Show.asciiTab63 */,_Nh/* GHC.Show.asciiTab3 */),
_Nk/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_Nl/* asciiTab1 */ = new T2(1,_Nk/* GHC.Show.asciiTab64 */,_Nj/* GHC.Show.asciiTab2 */),
_Nm/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_Nn/* asciiTab */ = new T2(1,_Nm/* GHC.Show.asciiTab65 */,_Nl/* GHC.Show.asciiTab1 */),
_No/* lvl */ = 92,
_Np/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_Nq/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_Nr/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_Ns/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_Nt/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_Nu/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_Nv/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_Nw/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_Nx/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_Ny/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_Nz/* $wshowLitChar */ = function(_NA/* sfeh */, _NB/* sfei */){
  if(_NA/* sfeh */<=127){
    var _NC/* sfel */ = E(_NA/* sfeh */);
    switch(_NC/* sfel */){
      case 92:
        return new F(function(){return _12/* GHC.Base.++ */(_Nr/* GHC.Show.lvl2 */, _NB/* sfei */);});
        break;
      case 127:
        return new F(function(){return _12/* GHC.Base.++ */(_Np/* GHC.Show.lvl1 */, _NB/* sfei */);});
        break;
      default:
        if(_NC/* sfel */<32){
          var _ND/* sfeo */ = E(_NC/* sfel */);
          switch(_ND/* sfeo */){
            case 7:
              return new F(function(){return _12/* GHC.Base.++ */(_Nq/* GHC.Show.lvl10 */, _NB/* sfei */);});
              break;
            case 8:
              return new F(function(){return _12/* GHC.Base.++ */(_Ny/* GHC.Show.lvl9 */, _NB/* sfei */);});
              break;
            case 9:
              return new F(function(){return _12/* GHC.Base.++ */(_Nx/* GHC.Show.lvl8 */, _NB/* sfei */);});
              break;
            case 10:
              return new F(function(){return _12/* GHC.Base.++ */(_Nw/* GHC.Show.lvl7 */, _NB/* sfei */);});
              break;
            case 11:
              return new F(function(){return _12/* GHC.Base.++ */(_Nv/* GHC.Show.lvl6 */, _NB/* sfei */);});
              break;
            case 12:
              return new F(function(){return _12/* GHC.Base.++ */(_Nu/* GHC.Show.lvl5 */, _NB/* sfei */);});
              break;
            case 13:
              return new F(function(){return _12/* GHC.Base.++ */(_Nt/* GHC.Show.lvl4 */, _NB/* sfei */);});
              break;
            case 14:
              return new F(function(){return _12/* GHC.Base.++ */(_Ns/* GHC.Show.lvl3 */, new T(function(){
                var _NE/* sfes */ = E(_NB/* sfei */);
                if(!_NE/* sfes */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_NE/* sfes */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _NE/* sfes */));
                  }else{
                    return E(_NE/* sfes */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _12/* GHC.Base.++ */(new T2(1,_No/* GHC.Show.lvl */,new T(function(){
                return B(_71/* GHC.List.$w!! */(_Nn/* GHC.Show.asciiTab */, _ND/* sfeo */));
              })), _NB/* sfei */);});
          }
        }else{
          return new T2(1,_NC/* sfel */,_NB/* sfei */);
        }
    }
  }else{
    var _NF/* sfeR */ = new T(function(){
      var _NG/* sfeC */ = jsShowI/* EXTERNAL */(_NA/* sfeh */);
      return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_NG/* sfeC */), new T(function(){
        var _NH/* sfeH */ = E(_NB/* sfei */);
        if(!_NH/* sfeH */._){
          return __Z/* EXTERNAL */;
        }else{
          var _NI/* sfeK */ = E(_NH/* sfeH */.a);
          if(_NI/* sfeK */<48){
            return E(_NH/* sfeH */);
          }else{
            if(_NI/* sfeK */>57){
              return E(_NH/* sfeH */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _NH/* sfeH */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_No/* GHC.Show.lvl */,_NF/* sfeR */);
  }
},
_NJ/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_NK/* showLitString */ = function(_NL/* sfeW */, _NM/* sfeX */){
  var _NN/* sfeY */ = E(_NL/* sfeW */);
  if(!_NN/* sfeY */._){
    return E(_NM/* sfeX */);
  }else{
    var _NO/* sff0 */ = _NN/* sfeY */.b,
    _NP/* sff3 */ = E(_NN/* sfeY */.a);
    if(_NP/* sff3 */==34){
      return new F(function(){return _12/* GHC.Base.++ */(_NJ/* GHC.Show.lvl11 */, new T(function(){
        return B(_NK/* GHC.Show.showLitString */(_NO/* sff0 */, _NM/* sfeX */));
      },1));});
    }else{
      return new F(function(){return _Nz/* GHC.Show.$wshowLitChar */(_NP/* sff3 */, new T(function(){
        return B(_NK/* GHC.Show.showLitString */(_NO/* sff0 */, _NM/* sfeX */));
      }));});
    }
  }
},
_LY/* $fShowFormElement_$cshow */ = function(_NQ/* s6Iv */){
  var _NR/* s6Iw */ = E(_NQ/* s6Iv */);
  switch(_NR/* s6Iw */._){
    case 0:
      var _NS/* s6ID */ = new T(function(){
        var _NT/* s6IC */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_Me/* FormEngine.FormElement.FormElement.lvl4 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_LV/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _NR/* s6Iw */.b, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _NT/* s6IC */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_M9/* FormEngine.FormElement.FormElement.lvl16 */, _NS/* s6ID */);});
      break;
    case 1:
      var _NU/* s6IF */ = _NR/* s6Iw */.b,
      _NV/* s6IT */ = new T(function(){
        var _NW/* s6IS */ = new T(function(){
          var _NX/* s6IR */ = new T(function(){
            var _NY/* s6IJ */ = E(_NR/* s6Iw */.c);
            if(!_NY/* s6IJ */._){
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, new T(function(){
                return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _NU/* s6IF */));
              },1)));
            }else{
              var _NZ/* s6IQ */ = new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_NY/* s6IJ */.a), _I/* GHC.Types.[] */)), new T(function(){
                  return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _NU/* s6IF */));
                },1)));
              },1);
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, _NZ/* s6IQ */));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _NX/* s6IR */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _NW/* s6IS */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_M8/* FormEngine.FormElement.FormElement.lvl15 */, _NV/* s6IT */);});
      break;
    case 2:
      var _O0/* s6IV */ = _NR/* s6Iw */.b,
      _O1/* s6J9 */ = new T(function(){
        var _O2/* s6J8 */ = new T(function(){
          var _O3/* s6J7 */ = new T(function(){
            var _O4/* s6IZ */ = E(_NR/* s6Iw */.c);
            if(!_O4/* s6IZ */._){
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, new T(function(){
                return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _O0/* s6IV */));
              },1)));
            }else{
              var _O5/* s6J6 */ = new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_O4/* s6IZ */.a), _I/* GHC.Types.[] */)), new T(function(){
                  return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _O0/* s6IV */));
                },1)));
              },1);
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, _O5/* s6J6 */));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _O3/* s6J7 */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _O2/* s6J8 */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_M7/* FormEngine.FormElement.FormElement.lvl14 */, _O1/* s6J9 */);});
      break;
    case 3:
      var _O6/* s6Jb */ = _NR/* s6Iw */.b,
      _O7/* s6Jp */ = new T(function(){
        var _O8/* s6Jo */ = new T(function(){
          var _O9/* s6Jn */ = new T(function(){
            var _Oa/* s6Jf */ = E(_NR/* s6Iw */.c);
            if(!_Oa/* s6Jf */._){
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, new T(function(){
                return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _O6/* s6Jb */));
              },1)));
            }else{
              var _Ob/* s6Jm */ = new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_Oa/* s6Jf */.a), _I/* GHC.Types.[] */)), new T(function(){
                  return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _O6/* s6Jb */));
                },1)));
              },1);
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, _Ob/* s6Jm */));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _O9/* s6Jn */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _O8/* s6Jo */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_M6/* FormEngine.FormElement.FormElement.lvl13 */, _O7/* s6Jp */);});
      break;
    case 4:
      var _Oc/* s6JX */ = new T(function(){
        var _Od/* s6JW */ = new T(function(){
          var _Oe/* s6JV */ = new T(function(){
            var _Of/* s6Jw */ = new T(function(){
              var _Og/* s6JO */ = new T(function(){
                var _Oh/* s6Jx */ = new T(function(){
                  var _Oi/* s6JC */ = new T(function(){
                    var _Oj/* s6Jy */ = E(_NR/* s6Iw */.c);
                    if(!_Oj/* s6Jy */._){
                      return E(_M0/* GHC.Show.$fShowMaybe3 */);
                    }else{
                      return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
                        return B(_NK/* GHC.Show.showLitString */(_Oj/* s6Jy */.a, _Mb/* FormEngine.FormElement.FormElement.lvl17 */));
                      }))));
                    }
                  },1);
                  return B(_12/* GHC.Base.++ */(_M4/* FormEngine.FormElement.FormElement.lvl11 */, _Oi/* s6JC */));
                }),
                _Ok/* s6JD */ = E(_NR/* s6Iw */.b);
                if(!_Ok/* s6JD */._){
                  return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, _Oh/* s6Jx */));
                }else{
                  return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T(function(){
                    var _Ol/* s6JI */ = jsShow/* EXTERNAL */(E(_Ok/* s6JD */.a));
                    return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_Ol/* s6JI */), _Oh/* s6Jx */));
                  },1)));
                }
              },1);
              return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _Og/* s6JO */));
            }),
            _Om/* s6JP */ = E(_NR/* s6Iw */.d);
            if(!_Om/* s6JP */._){
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, _Of/* s6Jw */));
            }else{
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_Om/* s6JP */.a), _I/* GHC.Types.[] */)), _Of/* s6Jw */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _Oe/* s6JV */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _Od/* s6JW */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_M5/* FormEngine.FormElement.FormElement.lvl12 */, _Oc/* s6JX */);});
      break;
    case 5:
      return new F(function(){return _12/* GHC.Base.++ */(_M3/* FormEngine.FormElement.FormElement.lvl10 */, new T(function(){
        return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */));
      },1));});
      break;
    case 6:
      var _On/* s6Kd */ = new T(function(){
        var _Oo/* s6Kc */ = new T(function(){
          var _Op/* s6Kb */ = new T(function(){
            var _Oq/* s6K6 */ = E(_NR/* s6Iw */.c);
            if(!_Oq/* s6K6 */._){
              return E(_M0/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_Oq/* s6K6 */.a), _I/* GHC.Types.[] */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _Op/* s6Kb */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _Oo/* s6Kc */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_Mj/* FormEngine.FormElement.FormElement.lvl9 */, _On/* s6Kd */);});
      break;
    case 7:
      var _Or/* s6Kx */ = new T(function(){
        var _Os/* s6Kw */ = new T(function(){
          var _Ot/* s6Kv */ = new T(function(){
            var _Ou/* s6Kj */ = new T(function(){
              var _Ov/* s6Ko */ = new T(function(){
                var _Ow/* s6Kk */ = E(_NR/* s6Iw */.b);
                if(!_Ow/* s6Kk */._){
                  return E(_M0/* GHC.Show.$fShowMaybe3 */);
                }else{
                  return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
                    return B(_NK/* GHC.Show.showLitString */(_Ow/* s6Kk */.a, _Mb/* FormEngine.FormElement.FormElement.lvl17 */));
                  }))));
                }
              },1);
              return B(_12/* GHC.Base.++ */(_Mh/* FormEngine.FormElement.FormElement.lvl7 */, _Ov/* s6Ko */));
            }),
            _Ox/* s6Kp */ = E(_NR/* s6Iw */.c);
            if(!_Ox/* s6Kp */._){
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, _Ou/* s6Kj */));
            }else{
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_Ox/* s6Kp */.a), _I/* GHC.Types.[] */)), _Ou/* s6Kj */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _Ot/* s6Kv */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _Os/* s6Kw */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_Mi/* FormEngine.FormElement.FormElement.lvl8 */, _Or/* s6Kx */);});
      break;
    case 8:
      var _Oy/* s6Kz */ = _NR/* s6Iw */.b,
      _Oz/* s6KP */ = new T(function(){
        var _OA/* s6KO */ = new T(function(){
          var _OB/* s6KN */ = new T(function(){
            var _OC/* s6KD */ = E(_NR/* s6Iw */.c);
            if(!_OC/* s6KD */._){
              var _OD/* s6KF */ = new T(function(){
                return B(_12/* GHC.Base.++ */(_Me/* FormEngine.FormElement.FormElement.lvl4 */, new T(function(){
                  return B(_26/* GHC.Show.showList__ */(_LV/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _Oy/* s6Kz */, _I/* GHC.Types.[] */));
                },1)));
              },1);
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, _OD/* s6KF */));
            }else{
              var _OE/* s6KM */ = new T(function(){
                var _OF/* s6KL */ = new T(function(){
                  return B(_12/* GHC.Base.++ */(_Me/* FormEngine.FormElement.FormElement.lvl4 */, new T(function(){
                    return B(_26/* GHC.Show.showList__ */(_LV/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _Oy/* s6Kz */, _I/* GHC.Types.[] */));
                  },1)));
                },1);
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_OC/* s6KD */.a), _I/* GHC.Types.[] */)), _OF/* s6KL */));
              },1);
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, _OE/* s6KM */));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _OB/* s6KN */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _OA/* s6KO */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_Mg/* FormEngine.FormElement.FormElement.lvl6 */, _Oz/* s6KP */);});
      break;
    case 9:
      var _OG/* s6KS */ = _NR/* s6Iw */.c,
      _OH/* s6L8 */ = new T(function(){
        var _OI/* s6L7 */ = new T(function(){
          var _OJ/* s6L6 */ = new T(function(){
            var _OK/* s6KW */ = E(_NR/* s6Iw */.d);
            if(!_OK/* s6KW */._){
              var _OL/* s6KY */ = new T(function(){
                return B(_12/* GHC.Base.++ */(_Me/* FormEngine.FormElement.FormElement.lvl4 */, new T(function(){
                  return B(_26/* GHC.Show.showList__ */(_LV/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _OG/* s6KS */, _I/* GHC.Types.[] */));
                },1)));
              },1);
              return B(_12/* GHC.Base.++ */(_M0/* GHC.Show.$fShowMaybe3 */, _OL/* s6KY */));
            }else{
              var _OM/* s6L5 */ = new T(function(){
                var _ON/* s6L4 */ = new T(function(){
                  return B(_12/* GHC.Base.++ */(_Me/* FormEngine.FormElement.FormElement.lvl4 */, new T(function(){
                    return B(_26/* GHC.Show.showList__ */(_LV/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _OG/* s6KS */, _I/* GHC.Types.[] */));
                  },1)));
                },1);
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_OK/* s6KW */.a), _I/* GHC.Types.[] */)), _ON/* s6L4 */));
              },1);
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, _OM/* s6L5 */));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _OJ/* s6L6 */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _OI/* s6L7 */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_Mf/* FormEngine.FormElement.FormElement.lvl5 */, _OH/* s6L8 */);});
      break;
    case 10:
      var _OO/* s6Ll */ = new T(function(){
        var _OP/* s6Lk */ = new T(function(){
          var _OQ/* s6Lj */ = new T(function(){
            var _OR/* s6Le */ = E(_NR/* s6Iw */.c);
            if(!_OR/* s6Le */._){
              return E(_M0/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_12/* GHC.Base.++ */(_LZ/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_OR/* s6Le */.a), _I/* GHC.Types.[] */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_Mc/* FormEngine.FormElement.FormElement.lvl2 */, _OQ/* s6Lj */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */)), _OP/* s6Lk */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_Md/* FormEngine.FormElement.FormElement.lvl3 */, _OO/* s6Ll */);});
      break;
    case 11:
      return new F(function(){return _12/* GHC.Base.++ */(_M2/* FormEngine.FormElement.FormElement.lvl1 */, new T(function(){
        return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */));
      },1));});
      break;
    default:
      return new F(function(){return _12/* GHC.Base.++ */(_M1/* FormEngine.FormElement.FormElement.lvl */, new T(function(){
        return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_NR/* s6Iw */));
      },1));});
  }
},
_OS/* lvl57 */ = new T2(1,_Ma/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_OT/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumValueRule (Float -> Bool)"));
}),
_OU/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ReadOnlyRule"));
}),
_OV/* shows_$cshowList */ = function(_OW/* sff6 */, _OX/* sff7 */){
  return new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
    return B(_NK/* GHC.Show.showLitString */(_OW/* sff6 */, new T2(1,_Ma/* GHC.Show.shows5 */,_OX/* sff7 */)));
  }));
},
_OY/* $fShowFormRule_$cshow */ = function(_OZ/* s5y7 */){
  var _P0/* s5y8 */ = E(_OZ/* s5y7 */);
  switch(_P0/* s5y8 */._){
    case 0:
      var _P1/* s5yf */ = new T(function(){
        var _P2/* s5ye */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
            return B(_NK/* GHC.Show.showLitString */(_P0/* s5y8 */.b, _OS/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_OV/* GHC.Show.shows_$cshowList */, _P0/* s5y8 */.a, _I/* GHC.Types.[] */)), _P2/* s5ye */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumRule @ ", _P1/* s5yf */);});
      break;
    case 1:
      var _P3/* s5ym */ = new T(function(){
        var _P4/* s5yl */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
            return B(_NK/* GHC.Show.showLitString */(_P0/* s5y8 */.b, _OS/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_OV/* GHC.Show.shows_$cshowList */, _P0/* s5y8 */.a, _I/* GHC.Types.[] */)), _P4/* s5yl */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumTBsRule @ ", _P3/* s5ym */);});
      break;
    case 2:
      var _P5/* s5yu */ = new T(function(){
        var _P6/* s5yt */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
            return B(_NK/* GHC.Show.showLitString */(_P0/* s5y8 */.b, _OS/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
          return B(_NK/* GHC.Show.showLitString */(_P0/* s5y8 */.a, _OS/* FormEngine.FormItem.lvl57 */));
        })), _P6/* s5yt */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("CopyValueRule @ ", _P5/* s5yu */);});
      break;
    case 3:
      return E(_OU/* FormEngine.FormItem.lvl7 */);
    default:
      return E(_OT/* FormEngine.FormItem.lvl6 */);
  }
},
_P7/* identity2element' */ = function(_P8/* sa3f */, _P9/* sa3g */){
  var _Pa/* sa3h */ = E(_P9/* sa3g */);
  if(!_Pa/* sa3h */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Pb/* sa3i */ = _Pa/* sa3h */.a,
    _Pc/* sa3v */ = function(_Pd/* sa3w */){
      var _Pe/* sa3y */ = B(_P7/* FormEngine.FormElement.Updating.identity2element' */(_P8/* sa3f */, B(_HK/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_Pb/* sa3i */))));
      if(!_Pe/* sa3y */._){
        return new F(function(){return _P7/* FormEngine.FormElement.Updating.identity2element' */(_P8/* sa3f */, _Pa/* sa3h */.b);});
      }else{
        return E(_Pe/* sa3y */);
      }
    },
    _Pf/* sa3A */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_Pb/* sa3i */)))).c);
    if(!_Pf/* sa3A */._){
      if(!B(_J9/* GHC.Base.eqString */(_I/* GHC.Types.[] */, _P8/* sa3f */))){
        return new F(function(){return _Pc/* sa3v */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Pb/* sa3i */);
      }
    }else{
      if(!B(_J9/* GHC.Base.eqString */(_Pf/* sa3A */.a, _P8/* sa3f */))){
        return new F(function(){return _Pc/* sa3v */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Pb/* sa3i */);
      }
    }
  }
},
_Pg/* getRadioValue2 */ = "(function (elId) { return $(elId); })",
_Ph/* getRadioValue3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\']:checked"));
}),
_Pi/* getRadioValue4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("[name=\'"));
}),
_Pj/* getRadioValue1 */ = function(_Pk/* stPf */, _/* EXTERNAL */){
  var _Pl/* stPq */ = eval/* EXTERNAL */(E(_Pg/* FormEngine.JQuery.getRadioValue2 */)),
  _Pm/* stPy */ = __app1/* EXTERNAL */(E(_Pl/* stPq */), toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Pi/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_Pk/* stPf */, _Ph/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _Pn/* stPE */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), _Pm/* stPy */);
  return new T(function(){
    var _Po/* stPI */ = String/* EXTERNAL */(_Pn/* stPE */);
    return fromJSStr/* EXTERNAL */(_Po/* stPI */);
  });
},
_Pp/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("undefined"));
}),
_Pq/* nfiUnitId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_unit"));
}),
_Pr/* readEither6 */ = function(_Ps/*  s2Rf3 */){
  while(1){
    var _Pt/*  readEither6 */ = B((function(_Pu/* s2Rf3 */){
      var _Pv/* s2Rf4 */ = E(_Pu/* s2Rf3 */);
      if(!_Pv/* s2Rf4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _Pw/* s2Rf6 */ = _Pv/* s2Rf4 */.b,
        _Px/* s2Rf7 */ = E(_Pv/* s2Rf4 */.a);
        if(!E(_Px/* s2Rf7 */.b)._){
          return new T2(1,_Px/* s2Rf7 */.a,new T(function(){
            return B(_Pr/* Text.Read.readEither6 */(_Pw/* s2Rf6 */));
          }));
        }else{
          _Ps/*  s2Rf3 */ = _Pw/* s2Rf6 */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_Ps/*  s2Rf3 */));
    if(_Pt/*  readEither6 */!=__continue/* EXTERNAL */){
      return _Pt/*  readEither6 */;
    }
  }
},
_Py/* run */ = function(_Pz/*  s1iAI */, _PA/*  s1iAJ */){
  while(1){
    var _PB/*  run */ = B((function(_PC/* s1iAI */, _PD/* s1iAJ */){
      var _PE/* s1iAK */ = E(_PC/* s1iAI */);
      switch(_PE/* s1iAK */._){
        case 0:
          var _PF/* s1iAM */ = E(_PD/* s1iAJ */);
          if(!_PF/* s1iAM */._){
            return __Z/* EXTERNAL */;
          }else{
            _Pz/*  s1iAI */ = B(A1(_PE/* s1iAK */.a,_PF/* s1iAM */.a));
            _PA/*  s1iAJ */ = _PF/* s1iAM */.b;
            return __continue/* EXTERNAL */;
          }
          break;
        case 1:
          var _PG/*   s1iAI */ = B(A1(_PE/* s1iAK */.a,_PD/* s1iAJ */)),
          _PH/*   s1iAJ */ = _PD/* s1iAJ */;
          _Pz/*  s1iAI */ = _PG/*   s1iAI */;
          _PA/*  s1iAJ */ = _PH/*   s1iAJ */;
          return __continue/* EXTERNAL */;
        case 2:
          return __Z/* EXTERNAL */;
        case 3:
          return new T2(1,new T2(0,_PE/* s1iAK */.a,_PD/* s1iAJ */),new T(function(){
            return B(_Py/* Text.ParserCombinators.ReadP.run */(_PE/* s1iAK */.b, _PD/* s1iAJ */));
          }));
        default:
          return E(_PE/* s1iAK */.a);
      }
    })(_Pz/*  s1iAI */, _PA/*  s1iAJ */));
    if(_PB/*  run */!=__continue/* EXTERNAL */){
      return _PB/*  run */;
    }
  }
},
_PI/* selectByName2 */ = "(function (name) { return $(\'[name=\"\' + name + \'\"]\'); })",
_PJ/* selectByName1 */ = function(_PK/* stMB */, _/* EXTERNAL */){
  var _PL/* stML */ = eval/* EXTERNAL */(E(_PI/* FormEngine.JQuery.selectByName2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_PL/* stML */), toJSStr/* EXTERNAL */(E(_PK/* stMB */)));});
},
_PM/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_PN/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_PO/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_PP/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_PM/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_PN/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_PO/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_PQ/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_PP/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_PR/* $fExceptionPatternMatchFail1 */ = function(_PS/* s4nv1 */){
  return E(_PQ/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_PT/* $fExceptionPatternMatchFail_$cfromException */ = function(_PU/* s4nvc */){
  var _PV/* s4nvd */ = E(_PU/* s4nvc */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_PV/* s4nvd */.a)), _PR/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _PV/* s4nvd */.b);});
},
_PW/* $fExceptionPatternMatchFail_$cshow */ = function(_PX/* s4nv4 */){
  return E(E(_PX/* s4nv4 */).a);
},
_PY/* $fExceptionPatternMatchFail_$ctoException */ = function(_PZ/* B1 */){
  return new T2(0,_Q0/* Control.Exception.Base.$fExceptionPatternMatchFail */,_PZ/* B1 */);
},
_Q1/* $fShowPatternMatchFail1 */ = function(_Q2/* s4nqK */, _Q3/* s4nqL */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_Q2/* s4nqK */).a, _Q3/* s4nqL */);});
},
_Q4/* $fShowPatternMatchFail_$cshowList */ = function(_Q5/* s4nv2 */, _Q6/* s4nv3 */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Q1/* Control.Exception.Base.$fShowPatternMatchFail1 */, _Q5/* s4nv2 */, _Q6/* s4nv3 */);});
},
_Q7/* $fShowPatternMatchFail_$cshowsPrec */ = function(_Q8/* s4nv7 */, _Q9/* s4nv8 */, _Qa/* s4nv9 */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_Q9/* s4nv8 */).a, _Qa/* s4nv9 */);});
},
_Qb/* $fShowPatternMatchFail */ = new T3(0,_Q7/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_PW/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_Q4/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_Q0/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_PR/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_Qb/* Control.Exception.Base.$fShowPatternMatchFail */,_PY/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_PT/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_PW/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_Qc/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_Qd/* lvl */ = function(_Qe/* s2SzX */, _Qf/* s2SzY */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_Qf/* s2SzY */, _Qe/* s2SzX */));
  }));});
},
_Qg/* throw1 */ = function(_Qh/* B2 */, _Qi/* B1 */){
  return new F(function(){return _Qd/* GHC.Exception.lvl */(_Qh/* B2 */, _Qi/* B1 */);});
},
_Qj/* $wspan */ = function(_Qk/* s9vU */, _Ql/* s9vV */){
  var _Qm/* s9vW */ = E(_Ql/* s9vV */);
  if(!_Qm/* s9vW */._){
    return new T2(0,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */);
  }else{
    var _Qn/* s9vX */ = _Qm/* s9vW */.a;
    if(!B(A1(_Qk/* s9vU */,_Qn/* s9vX */))){
      return new T2(0,_I/* GHC.Types.[] */,_Qm/* s9vW */);
    }else{
      var _Qo/* s9w0 */ = new T(function(){
        var _Qp/* s9w1 */ = B(_Qj/* GHC.List.$wspan */(_Qk/* s9vU */, _Qm/* s9vW */.b));
        return new T2(0,_Qp/* s9w1 */.a,_Qp/* s9w1 */.b);
      });
      return new T2(0,new T2(1,_Qn/* s9vX */,new T(function(){
        return E(E(_Qo/* s9w0 */).a);
      })),new T(function(){
        return E(E(_Qo/* s9w0 */).b);
      }));
    }
  }
},
_Qq/* untangle1 */ = 32,
_Qr/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_Qs/* untangle3 */ = function(_Qt/* s3K4R */){
  return (E(_Qt/* s3K4R */)==124) ? false : true;
},
_Qu/* untangle */ = function(_Qv/* s3K5K */, _Qw/* s3K5L */){
  var _Qx/* s3K5N */ = B(_Qj/* GHC.List.$wspan */(_Qs/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_Qv/* s3K5K */)))),
  _Qy/* s3K5O */ = _Qx/* s3K5N */.a,
  _Qz/* s3K5Q */ = function(_QA/* s3K5R */, _QB/* s3K5S */){
    var _QC/* s3K5V */ = new T(function(){
      var _QD/* s3K5U */ = new T(function(){
        return B(_12/* GHC.Base.++ */(_Qw/* s3K5L */, new T(function(){
          return B(_12/* GHC.Base.++ */(_QB/* s3K5S */, _Qr/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _QD/* s3K5U */));
    },1);
    return new F(function(){return _12/* GHC.Base.++ */(_QA/* s3K5R */, _QC/* s3K5V */);});
  },
  _QE/* s3K5W */ = E(_Qx/* s3K5N */.b);
  if(!_QE/* s3K5W */._){
    return new F(function(){return _Qz/* s3K5Q */(_Qy/* s3K5O */, _I/* GHC.Types.[] */);});
  }else{
    if(E(_QE/* s3K5W */.a)==124){
      return new F(function(){return _Qz/* s3K5Q */(_Qy/* s3K5O */, new T2(1,_Qq/* GHC.IO.Exception.untangle1 */,_QE/* s3K5W */.b));});
    }else{
      return new F(function(){return _Qz/* s3K5Q */(_Qy/* s3K5O */, _I/* GHC.Types.[] */);});
    }
  }
},
_QF/* patError */ = function(_QG/* s4nwI */){
  return new F(function(){return _Qg/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_Qu/* GHC.IO.Exception.untangle */(_QG/* s4nwI */, _Qc/* Control.Exception.Base.lvl3 */));
  })), _Q0/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_QH/* lvl2 */ = new T(function(){
  return B(_QF/* Control.Exception.Base.patError */("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));
}),
_QI/* $fAlternativeP_$c<|> */ = function(_QJ/* s1iBo */, _QK/* s1iBp */){
  var _QL/* s1iBq */ = function(_QM/* s1iBr */){
    var _QN/* s1iBs */ = E(_QK/* s1iBp */);
    if(_QN/* s1iBs */._==3){
      return new T2(3,_QN/* s1iBs */.a,new T(function(){
        return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_QJ/* s1iBo */, _QN/* s1iBs */.b));
      }));
    }else{
      var _QO/* s1iBt */ = E(_QJ/* s1iBo */);
      if(_QO/* s1iBt */._==2){
        return E(_QN/* s1iBs */);
      }else{
        var _QP/* s1iBu */ = E(_QN/* s1iBs */);
        if(_QP/* s1iBu */._==2){
          return E(_QO/* s1iBt */);
        }else{
          var _QQ/* s1iBv */ = function(_QR/* s1iBw */){
            var _QS/* s1iBx */ = E(_QP/* s1iBu */);
            if(_QS/* s1iBx */._==4){
              var _QT/* s1iBU */ = function(_QU/* s1iBR */){
                return new T1(4,new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_Py/* Text.ParserCombinators.ReadP.run */(_QO/* s1iBt */, _QU/* s1iBR */)), _QS/* s1iBx */.a));
                }));
              };
              return new T1(1,_QT/* s1iBU */);
            }else{
              var _QV/* s1iBy */ = E(_QO/* s1iBt */);
              if(_QV/* s1iBy */._==1){
                var _QW/* s1iBF */ = _QV/* s1iBy */.a,
                _QX/* s1iBG */ = E(_QS/* s1iBx */);
                if(!_QX/* s1iBG */._){
                  return new T1(1,function(_QY/* s1iBI */){
                    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_QW/* s1iBF */,_QY/* s1iBI */)), _QX/* s1iBG */);});
                  });
                }else{
                  var _QZ/* s1iBP */ = function(_R0/* s1iBM */){
                    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_QW/* s1iBF */,_R0/* s1iBM */)), new T(function(){
                      return B(A1(_QX/* s1iBG */.a,_R0/* s1iBM */));
                    }));});
                  };
                  return new T1(1,_QZ/* s1iBP */);
                }
              }else{
                var _R1/* s1iBz */ = E(_QS/* s1iBx */);
                if(!_R1/* s1iBz */._){
                  return E(_QH/* Text.ParserCombinators.ReadP.lvl2 */);
                }else{
                  var _R2/* s1iBE */ = function(_R3/* s1iBC */){
                    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_QV/* s1iBy */, new T(function(){
                      return B(A1(_R1/* s1iBz */.a,_R3/* s1iBC */));
                    }));});
                  };
                  return new T1(1,_R2/* s1iBE */);
                }
              }
            }
          },
          _R4/* s1iBV */ = E(_QO/* s1iBt */);
          switch(_R4/* s1iBV */._){
            case 1:
              var _R5/* s1iBX */ = E(_QP/* s1iBu */);
              if(_R5/* s1iBX */._==4){
                var _R6/* s1iC3 */ = function(_R7/* s1iBZ */){
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_Py/* Text.ParserCombinators.ReadP.run */(B(A1(_R4/* s1iBV */.a,_R7/* s1iBZ */)), _R7/* s1iBZ */)), _R5/* s1iBX */.a));
                  }));
                };
                return new T1(1,_R6/* s1iC3 */);
              }else{
                return new F(function(){return _QQ/* s1iBv */(_/* EXTERNAL */);});
              }
              break;
            case 4:
              var _R8/* s1iC4 */ = _R4/* s1iBV */.a,
              _R9/* s1iC5 */ = E(_QP/* s1iBu */);
              switch(_R9/* s1iC5 */._){
                case 0:
                  var _Ra/* s1iCa */ = function(_Rb/* s1iC7 */){
                    var _Rc/* s1iC9 */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_R8/* s1iC4 */, new T(function(){
                        return B(_Py/* Text.ParserCombinators.ReadP.run */(_R9/* s1iC5 */, _Rb/* s1iC7 */));
                      },1)));
                    });
                    return new T1(4,_Rc/* s1iC9 */);
                  };
                  return new T1(1,_Ra/* s1iCa */);
                case 1:
                  var _Rd/* s1iCg */ = function(_Re/* s1iCc */){
                    var _Rf/* s1iCf */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_R8/* s1iC4 */, new T(function(){
                        return B(_Py/* Text.ParserCombinators.ReadP.run */(B(A1(_R9/* s1iC5 */.a,_Re/* s1iCc */)), _Re/* s1iCc */));
                      },1)));
                    });
                    return new T1(4,_Rf/* s1iCf */);
                  };
                  return new T1(1,_Rd/* s1iCg */);
                default:
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(_R8/* s1iC4 */, _R9/* s1iC5 */.a));
                  }));
              }
              break;
            default:
              return new F(function(){return _QQ/* s1iBv */(_/* EXTERNAL */);});
          }
        }
      }
    }
  },
  _Rg/* s1iCm */ = E(_QJ/* s1iBo */);
  switch(_Rg/* s1iCm */._){
    case 0:
      var _Rh/* s1iCo */ = E(_QK/* s1iBp */);
      if(!_Rh/* s1iCo */._){
        var _Ri/* s1iCt */ = function(_Rj/* s1iCq */){
          return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_Rg/* s1iCm */.a,_Rj/* s1iCq */)), new T(function(){
            return B(A1(_Rh/* s1iCo */.a,_Rj/* s1iCq */));
          }));});
        };
        return new T1(0,_Ri/* s1iCt */);
      }else{
        return new F(function(){return _QL/* s1iBq */(_/* EXTERNAL */);});
      }
      break;
    case 3:
      return new T2(3,_Rg/* s1iCm */.a,new T(function(){
        return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_Rg/* s1iCm */.b, _QK/* s1iBp */));
      }));
    default:
      return new F(function(){return _QL/* s1iBq */(_/* EXTERNAL */);});
  }
},
_Rk/* $fRead(,)3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_Rl/* $fRead(,)4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Rm/* $fEqChar_$c/= */ = function(_Rn/* scFn */, _Ro/* scFo */){
  return E(_Rn/* scFn */)!=E(_Ro/* scFo */);
},
_Rp/* $fEqChar_$c== */ = function(_Rq/* scFu */, _Rr/* scFv */){
  return E(_Rq/* scFu */)==E(_Rr/* scFv */);
},
_Rs/* $fEqChar */ = new T2(0,_Rp/* GHC.Classes.$fEqChar_$c== */,_Rm/* GHC.Classes.$fEqChar_$c/= */),
_Rt/* $fEq[]_$s$c==1 */ = function(_Ru/* scIY */, _Rv/* scIZ */){
  while(1){
    var _Rw/* scJ0 */ = E(_Ru/* scIY */);
    if(!_Rw/* scJ0 */._){
      return (E(_Rv/* scIZ */)._==0) ? true : false;
    }else{
      var _Rx/* scJ6 */ = E(_Rv/* scIZ */);
      if(!_Rx/* scJ6 */._){
        return false;
      }else{
        if(E(_Rw/* scJ0 */.a)!=E(_Rx/* scJ6 */.a)){
          return false;
        }else{
          _Ru/* scIY */ = _Rw/* scJ0 */.b;
          _Rv/* scIZ */ = _Rx/* scJ6 */.b;
          continue;
        }
      }
    }
  }
},
_Ry/* $fEq[]_$s$c/=1 */ = function(_Rz/* scJE */, _RA/* scJF */){
  return (!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_Rz/* scJE */, _RA/* scJF */))) ? true : false;
},
_RB/* $fEq[]_$s$fEq[]1 */ = new T2(0,_Rt/* GHC.Classes.$fEq[]_$s$c==1 */,_Ry/* GHC.Classes.$fEq[]_$s$c/=1 */),
_RC/* $fAlternativeP_$c>>= */ = function(_RD/* s1iCx */, _RE/* s1iCy */){
  var _RF/* s1iCz */ = E(_RD/* s1iCx */);
  switch(_RF/* s1iCz */._){
    case 0:
      return new T1(0,function(_RG/* s1iCB */){
        return new F(function(){return _RC/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_RF/* s1iCz */.a,_RG/* s1iCB */)), _RE/* s1iCy */);});
      });
    case 1:
      return new T1(1,function(_RH/* s1iCF */){
        return new F(function(){return _RC/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_RF/* s1iCz */.a,_RH/* s1iCF */)), _RE/* s1iCy */);});
      });
    case 2:
      return new T0(2);
    case 3:
      return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_RE/* s1iCy */,_RF/* s1iCz */.a)), new T(function(){
        return B(_RC/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_RF/* s1iCz */.b, _RE/* s1iCy */));
      }));});
      break;
    default:
      var _RI/* s1iCN */ = function(_RJ/* s1iCO */){
        var _RK/* s1iCP */ = E(_RJ/* s1iCO */);
        if(!_RK/* s1iCP */._){
          return __Z/* EXTERNAL */;
        }else{
          var _RL/* s1iCS */ = E(_RK/* s1iCP */.a);
          return new F(function(){return _12/* GHC.Base.++ */(B(_Py/* Text.ParserCombinators.ReadP.run */(B(A1(_RE/* s1iCy */,_RL/* s1iCS */.a)), _RL/* s1iCS */.b)), new T(function(){
            return B(_RI/* s1iCN */(_RK/* s1iCP */.b));
          },1));});
        }
      },
      _RM/* s1iCY */ = B(_RI/* s1iCN */(_RF/* s1iCz */.a));
      return (_RM/* s1iCY */._==0) ? new T0(2) : new T1(4,_RM/* s1iCY */);
  }
},
_RN/* Fail */ = new T0(2),
_RO/* $fApplicativeP_$creturn */ = function(_RP/* s1iBl */){
  return new T2(3,_RP/* s1iBl */,_RN/* Text.ParserCombinators.ReadP.Fail */);
},
_RQ/* <++2 */ = function(_RR/* s1iyp */, _RS/* s1iyq */){
  var _RT/* s1iyr */ = E(_RR/* s1iyp */);
  if(!_RT/* s1iyr */){
    return new F(function(){return A1(_RS/* s1iyq */,_0/* GHC.Tuple.() */);});
  }else{
    var _RU/* s1iys */ = new T(function(){
      return B(_RQ/* Text.ParserCombinators.ReadP.<++2 */(_RT/* s1iyr */-1|0, _RS/* s1iyq */));
    });
    return new T1(0,function(_RV/* s1iyu */){
      return E(_RU/* s1iys */);
    });
  }
},
_RW/* $wa */ = function(_RX/* s1iD8 */, _RY/* s1iD9 */, _RZ/* s1iDa */){
  var _S0/* s1iDb */ = new T(function(){
    return B(A1(_RX/* s1iD8 */,_RO/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
  }),
  _S1/* s1iDc */ = function(_S2/*  s1iDd */, _S3/*  s1iDe */, _S4/*  s1iDf */, _S5/*  s1iDg */){
    while(1){
      var _S6/*  s1iDc */ = B((function(_S7/* s1iDd */, _S8/* s1iDe */, _S9/* s1iDf */, _Sa/* s1iDg */){
        var _Sb/* s1iDh */ = E(_S7/* s1iDd */);
        switch(_Sb/* s1iDh */._){
          case 0:
            var _Sc/* s1iDj */ = E(_S8/* s1iDe */);
            if(!_Sc/* s1iDj */._){
              return new F(function(){return A1(_RY/* s1iD9 */,_Sa/* s1iDg */);});
            }else{
              var _Sd/*   s1iDf */ = _S9/* s1iDf */+1|0,
              _Se/*   s1iDg */ = _Sa/* s1iDg */;
              _S2/*  s1iDd */ = B(A1(_Sb/* s1iDh */.a,_Sc/* s1iDj */.a));
              _S3/*  s1iDe */ = _Sc/* s1iDj */.b;
              _S4/*  s1iDf */ = _Sd/*   s1iDf */;
              _S5/*  s1iDg */ = _Se/*   s1iDg */;
              return __continue/* EXTERNAL */;
            }
            break;
          case 1:
            var _Sf/*   s1iDd */ = B(A1(_Sb/* s1iDh */.a,_S8/* s1iDe */)),
            _Sg/*   s1iDe */ = _S8/* s1iDe */,
            _Sd/*   s1iDf */ = _S9/* s1iDf */,
            _Se/*   s1iDg */ = _Sa/* s1iDg */;
            _S2/*  s1iDd */ = _Sf/*   s1iDd */;
            _S3/*  s1iDe */ = _Sg/*   s1iDe */;
            _S4/*  s1iDf */ = _Sd/*   s1iDf */;
            _S5/*  s1iDg */ = _Se/*   s1iDg */;
            return __continue/* EXTERNAL */;
          case 2:
            return new F(function(){return A1(_RY/* s1iD9 */,_Sa/* s1iDg */);});
            break;
          case 3:
            var _Sh/* s1iDs */ = new T(function(){
              return B(_RC/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Sb/* s1iDh */, _Sa/* s1iDg */));
            });
            return new F(function(){return _RQ/* Text.ParserCombinators.ReadP.<++2 */(_S9/* s1iDf */, function(_Si/* s1iDt */){
              return E(_Sh/* s1iDs */);
            });});
            break;
          default:
            return new F(function(){return _RC/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Sb/* s1iDh */, _Sa/* s1iDg */);});
        }
      })(_S2/*  s1iDd */, _S3/*  s1iDe */, _S4/*  s1iDf */, _S5/*  s1iDg */));
      if(_S6/*  s1iDc */!=__continue/* EXTERNAL */){
        return _S6/*  s1iDc */;
      }
    }
  };
  return function(_Sj/* s1iDw */){
    return new F(function(){return _S1/* s1iDc */(_S0/* s1iDb */, _Sj/* s1iDw */, 0, _RZ/* s1iDa */);});
  };
},
_Sk/* munch3 */ = function(_Sl/* s1iyo */){
  return new F(function(){return A1(_Sl/* s1iyo */,_I/* GHC.Types.[] */);});
},
_Sm/* $wa3 */ = function(_Sn/* s1iyQ */, _So/* s1iyR */){
  var _Sp/* s1iyS */ = function(_Sq/* s1iyT */){
    var _Sr/* s1iyU */ = E(_Sq/* s1iyT */);
    if(!_Sr/* s1iyU */._){
      return E(_Sk/* Text.ParserCombinators.ReadP.munch3 */);
    }else{
      var _Ss/* s1iyV */ = _Sr/* s1iyU */.a;
      if(!B(A1(_Sn/* s1iyQ */,_Ss/* s1iyV */))){
        return E(_Sk/* Text.ParserCombinators.ReadP.munch3 */);
      }else{
        var _St/* s1iyY */ = new T(function(){
          return B(_Sp/* s1iyS */(_Sr/* s1iyU */.b));
        }),
        _Su/* s1iz6 */ = function(_Sv/* s1iyZ */){
          var _Sw/* s1iz0 */ = new T(function(){
            return B(A1(_St/* s1iyY */,function(_Sx/* s1iz1 */){
              return new F(function(){return A1(_Sv/* s1iyZ */,new T2(1,_Ss/* s1iyV */,_Sx/* s1iz1 */));});
            }));
          });
          return new T1(0,function(_Sy/* s1iz4 */){
            return E(_Sw/* s1iz0 */);
          });
        };
        return E(_Su/* s1iz6 */);
      }
    }
  };
  return function(_Sz/* s1iz7 */){
    return new F(function(){return A2(_Sp/* s1iyS */,_Sz/* s1iz7 */, _So/* s1iyR */);});
  };
},
_SA/* EOF */ = new T0(6),
_SB/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("valDig: Bad base"));
}),
_SC/* readDecP2 */ = new T(function(){
  return B(err/* EXTERNAL */(_SB/* Text.Read.Lex.lvl37 */));
}),
_SD/* $wa6 */ = function(_SE/* s1oaO */, _SF/* s1oaP */){
  var _SG/* s1oaQ */ = function(_SH/* s1oaR */, _SI/* s1oaS */){
    var _SJ/* s1oaT */ = E(_SH/* s1oaR */);
    if(!_SJ/* s1oaT */._){
      var _SK/* s1oaU */ = new T(function(){
        return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
      });
      return function(_SL/* s1oaV */){
        return new F(function(){return A1(_SL/* s1oaV */,_SK/* s1oaU */);});
      };
    }else{
      var _SM/* s1ob1 */ = E(_SJ/* s1oaT */.a),
      _SN/* s1ob3 */ = function(_SO/* s1ob4 */){
        var _SP/* s1ob5 */ = new T(function(){
          return B(_SG/* s1oaQ */(_SJ/* s1oaT */.b, function(_SQ/* s1ob6 */){
            return new F(function(){return A1(_SI/* s1oaS */,new T2(1,_SO/* s1ob4 */,_SQ/* s1ob6 */));});
          }));
        }),
        _SR/* s1obd */ = function(_SS/* s1ob9 */){
          var _ST/* s1oba */ = new T(function(){
            return B(A1(_SP/* s1ob5 */,_SS/* s1ob9 */));
          });
          return new T1(0,function(_SU/* s1obb */){
            return E(_ST/* s1oba */);
          });
        };
        return E(_SR/* s1obd */);
      };
      switch(E(_SE/* s1oaO */)){
        case 8:
          if(48>_SM/* s1ob1 */){
            var _SV/* s1obi */ = new T(function(){
              return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_SW/* s1obj */){
              return new F(function(){return A1(_SW/* s1obj */,_SV/* s1obi */);});
            };
          }else{
            if(_SM/* s1ob1 */>55){
              var _SX/* s1obn */ = new T(function(){
                return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_SY/* s1obo */){
                return new F(function(){return A1(_SY/* s1obo */,_SX/* s1obn */);});
              };
            }else{
              return new F(function(){return _SN/* s1ob3 */(_SM/* s1ob1 */-48|0);});
            }
          }
          break;
        case 10:
          if(48>_SM/* s1ob1 */){
            var _SZ/* s1obv */ = new T(function(){
              return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_T0/* s1obw */){
              return new F(function(){return A1(_T0/* s1obw */,_SZ/* s1obv */);});
            };
          }else{
            if(_SM/* s1ob1 */>57){
              var _T1/* s1obA */ = new T(function(){
                return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_T2/* s1obB */){
                return new F(function(){return A1(_T2/* s1obB */,_T1/* s1obA */);});
              };
            }else{
              return new F(function(){return _SN/* s1ob3 */(_SM/* s1ob1 */-48|0);});
            }
          }
          break;
        case 16:
          if(48>_SM/* s1ob1 */){
            if(97>_SM/* s1ob1 */){
              if(65>_SM/* s1ob1 */){
                var _T3/* s1obM */ = new T(function(){
                  return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                });
                return function(_T4/* s1obN */){
                  return new F(function(){return A1(_T4/* s1obN */,_T3/* s1obM */);});
                };
              }else{
                if(_SM/* s1ob1 */>70){
                  var _T5/* s1obR */ = new T(function(){
                    return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_T6/* s1obS */){
                    return new F(function(){return A1(_T6/* s1obS */,_T5/* s1obR */);});
                  };
                }else{
                  return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-65|0)+10|0);});
                }
              }
            }else{
              if(_SM/* s1ob1 */>102){
                if(65>_SM/* s1ob1 */){
                  var _T7/* s1oc2 */ = new T(function(){
                    return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_T8/* s1oc3 */){
                    return new F(function(){return A1(_T8/* s1oc3 */,_T7/* s1oc2 */);});
                  };
                }else{
                  if(_SM/* s1ob1 */>70){
                    var _T9/* s1oc7 */ = new T(function(){
                      return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Ta/* s1oc8 */){
                      return new F(function(){return A1(_Ta/* s1oc8 */,_T9/* s1oc7 */);});
                    };
                  }else{
                    return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-97|0)+10|0);});
              }
            }
          }else{
            if(_SM/* s1ob1 */>57){
              if(97>_SM/* s1ob1 */){
                if(65>_SM/* s1ob1 */){
                  var _Tb/* s1oco */ = new T(function(){
                    return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_Tc/* s1ocp */){
                    return new F(function(){return A1(_Tc/* s1ocp */,_Tb/* s1oco */);});
                  };
                }else{
                  if(_SM/* s1ob1 */>70){
                    var _Td/* s1oct */ = new T(function(){
                      return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Te/* s1ocu */){
                      return new F(function(){return A1(_Te/* s1ocu */,_Td/* s1oct */);});
                    };
                  }else{
                    return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                if(_SM/* s1ob1 */>102){
                  if(65>_SM/* s1ob1 */){
                    var _Tf/* s1ocE */ = new T(function(){
                      return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Tg/* s1ocF */){
                      return new F(function(){return A1(_Tg/* s1ocF */,_Tf/* s1ocE */);});
                    };
                  }else{
                    if(_SM/* s1ob1 */>70){
                      var _Th/* s1ocJ */ = new T(function(){
                        return B(A1(_SI/* s1oaS */,_I/* GHC.Types.[] */));
                      });
                      return function(_Ti/* s1ocK */){
                        return new F(function(){return A1(_Ti/* s1ocK */,_Th/* s1ocJ */);});
                      };
                    }else{
                      return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-65|0)+10|0);});
                    }
                  }
                }else{
                  return new F(function(){return _SN/* s1ob3 */((_SM/* s1ob1 */-97|0)+10|0);});
                }
              }
            }else{
              return new F(function(){return _SN/* s1ob3 */(_SM/* s1ob1 */-48|0);});
            }
          }
          break;
        default:
          return E(_SC/* Text.Read.Lex.readDecP2 */);
      }
    }
  },
  _Tj/* s1ocX */ = function(_Tk/* s1ocY */){
    var _Tl/* s1ocZ */ = E(_Tk/* s1ocY */);
    if(!_Tl/* s1ocZ */._){
      return new T0(2);
    }else{
      return new F(function(){return A1(_SF/* s1oaP */,_Tl/* s1ocZ */);});
    }
  };
  return function(_Tm/* s1od2 */){
    return new F(function(){return A3(_SG/* s1oaQ */,_Tm/* s1od2 */, _4/* GHC.Base.id */, _Tj/* s1ocX */);});
  };
},
_Tn/* lvl41 */ = 16,
_To/* lvl42 */ = 8,
_Tp/* $wa7 */ = function(_Tq/* s1od4 */){
  var _Tr/* s1od5 */ = function(_Ts/* s1od6 */){
    return new F(function(){return A1(_Tq/* s1od4 */,new T1(5,new T2(0,_To/* Text.Read.Lex.lvl42 */,_Ts/* s1od6 */)));});
  },
  _Tt/* s1od9 */ = function(_Tu/* s1oda */){
    return new F(function(){return A1(_Tq/* s1od4 */,new T1(5,new T2(0,_Tn/* Text.Read.Lex.lvl41 */,_Tu/* s1oda */)));});
  },
  _Tv/* s1odd */ = function(_Tw/* s1ode */){
    switch(E(_Tw/* s1ode */)){
      case 79:
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_To/* Text.Read.Lex.lvl42 */, _Tr/* s1od5 */)));
      case 88:
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_Tn/* Text.Read.Lex.lvl41 */, _Tt/* s1od9 */)));
      case 111:
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_To/* Text.Read.Lex.lvl42 */, _Tr/* s1od5 */)));
      case 120:
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_Tn/* Text.Read.Lex.lvl41 */, _Tt/* s1od9 */)));
      default:
        return new T0(2);
    }
  };
  return function(_Tx/* s1odr */){
    return (E(_Tx/* s1odr */)==48) ? E(new T1(0,_Tv/* s1odd */)) : new T0(2);
  };
},
_Ty/* a2 */ = function(_Tz/* s1odw */){
  return new T1(0,B(_Tp/* Text.Read.Lex.$wa7 */(_Tz/* s1odw */)));
},
_TA/* a */ = function(_TB/* s1o94 */){
  return new F(function(){return A1(_TB/* s1o94 */,_2o/* GHC.Base.Nothing */);});
},
_TC/* a1 */ = function(_TD/* s1o95 */){
  return new F(function(){return A1(_TD/* s1o95 */,_2o/* GHC.Base.Nothing */);});
},
_TE/* lvl */ = 10,
_TF/* log2I1 */ = new T1(0,1),
_TG/* lvl2 */ = new T1(0,2147483647),
_TH/* plusInteger */ = function(_TI/* s1Qe */, _TJ/* s1Qf */){
  while(1){
    var _TK/* s1Qg */ = E(_TI/* s1Qe */);
    if(!_TK/* s1Qg */._){
      var _TL/* s1Qh */ = _TK/* s1Qg */.a,
      _TM/* s1Qi */ = E(_TJ/* s1Qf */);
      if(!_TM/* s1Qi */._){
        var _TN/* s1Qj */ = _TM/* s1Qi */.a,
        _TO/* s1Qk */ = addC/* EXTERNAL */(_TL/* s1Qh */, _TN/* s1Qj */);
        if(!E(_TO/* s1Qk */.b)){
          return new T1(0,_TO/* s1Qk */.a);
        }else{
          _TI/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_TL/* s1Qh */));
          _TJ/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_TN/* s1Qj */));
          continue;
        }
      }else{
        _TI/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_TL/* s1Qh */));
        _TJ/* s1Qf */ = _TM/* s1Qi */;
        continue;
      }
    }else{
      var _TP/* s1Qz */ = E(_TJ/* s1Qf */);
      if(!_TP/* s1Qz */._){
        _TI/* s1Qe */ = _TK/* s1Qg */;
        _TJ/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_TP/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_TK/* s1Qg */.a, _TP/* s1Qz */.a));
      }
    }
  }
},
_TQ/* lvl3 */ = new T(function(){
  return B(_TH/* GHC.Integer.Type.plusInteger */(_TG/* GHC.Integer.Type.lvl2 */, _TF/* GHC.Integer.Type.log2I1 */));
}),
_TR/* negateInteger */ = function(_TS/* s1QH */){
  var _TT/* s1QI */ = E(_TS/* s1QH */);
  if(!_TT/* s1QI */._){
    var _TU/* s1QK */ = E(_TT/* s1QI */.a);
    return (_TU/* s1QK */==(-2147483648)) ? E(_TQ/* GHC.Integer.Type.lvl3 */) : new T1(0, -_TU/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_TT/* s1QI */.a));
  }
},
_TV/* numberToFixed1 */ = new T1(0,10),
_TW/* $wlenAcc */ = function(_TX/* s9Bd */, _TY/* s9Be */){
  while(1){
    var _TZ/* s9Bf */ = E(_TX/* s9Bd */);
    if(!_TZ/* s9Bf */._){
      return E(_TY/* s9Be */);
    }else{
      var _U0/*  s9Be */ = _TY/* s9Be */+1|0;
      _TX/* s9Bd */ = _TZ/* s9Bf */.b;
      _TY/* s9Be */ = _U0/*  s9Be */;
      continue;
    }
  }
},
_U1/* smallInteger */ = function(_U2/* B1 */){
  return new T1(0,_U2/* B1 */);
},
_U3/* numberToFixed2 */ = function(_U4/* s1o9e */){
  return new F(function(){return _U1/* GHC.Integer.Type.smallInteger */(E(_U4/* s1o9e */));});
},
_U5/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("this should not happen"));
}),
_U6/* lvl40 */ = new T(function(){
  return B(err/* EXTERNAL */(_U5/* Text.Read.Lex.lvl39 */));
}),
_U7/* timesInteger */ = function(_U8/* s1PN */, _U9/* s1PO */){
  while(1){
    var _Ua/* s1PP */ = E(_U8/* s1PN */);
    if(!_Ua/* s1PP */._){
      var _Ub/* s1PQ */ = _Ua/* s1PP */.a,
      _Uc/* s1PR */ = E(_U9/* s1PO */);
      if(!_Uc/* s1PR */._){
        var _Ud/* s1PS */ = _Uc/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_Ub/* s1PQ */, _Ud/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_Ub/* s1PQ */, _Ud/* s1PS */)|0);
        }else{
          _U8/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Ub/* s1PQ */));
          _U9/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Ud/* s1PS */));
          continue;
        }
      }else{
        _U8/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Ub/* s1PQ */));
        _U9/* s1PO */ = _Uc/* s1PR */;
        continue;
      }
    }else{
      var _Ue/* s1Q6 */ = E(_U9/* s1PO */);
      if(!_Ue/* s1Q6 */._){
        _U8/* s1PN */ = _Ua/* s1PP */;
        _U9/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Ue/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_Ua/* s1PP */.a, _Ue/* s1Q6 */.a));
      }
    }
  }
},
_Uf/* combine */ = function(_Ug/* s1o9h */, _Uh/* s1o9i */){
  var _Ui/* s1o9j */ = E(_Uh/* s1o9i */);
  if(!_Ui/* s1o9j */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Uj/* s1o9m */ = E(_Ui/* s1o9j */.b);
    return (_Uj/* s1o9m */._==0) ? E(_U6/* Text.Read.Lex.lvl40 */) : new T2(1,B(_TH/* GHC.Integer.Type.plusInteger */(B(_U7/* GHC.Integer.Type.timesInteger */(_Ui/* s1o9j */.a, _Ug/* s1o9h */)), _Uj/* s1o9m */.a)),new T(function(){
      return B(_Uf/* Text.Read.Lex.combine */(_Ug/* s1o9h */, _Uj/* s1o9m */.b));
    }));
  }
},
_Uk/* numberToFixed3 */ = new T1(0,0),
_Ul/* numberToFixed_go */ = function(_Um/*  s1o9s */, _Un/*  s1o9t */, _Uo/*  s1o9u */){
  while(1){
    var _Up/*  numberToFixed_go */ = B((function(_Uq/* s1o9s */, _Ur/* s1o9t */, _Us/* s1o9u */){
      var _Ut/* s1o9v */ = E(_Us/* s1o9u */);
      if(!_Ut/* s1o9v */._){
        return E(_Uk/* Text.Read.Lex.numberToFixed3 */);
      }else{
        if(!E(_Ut/* s1o9v */.b)._){
          return E(_Ut/* s1o9v */.a);
        }else{
          var _Uu/* s1o9B */ = E(_Ur/* s1o9t */);
          if(_Uu/* s1o9B */<=40){
            var _Uv/* s1o9F */ = function(_Uw/* s1o9G */, _Ux/* s1o9H */){
              while(1){
                var _Uy/* s1o9I */ = E(_Ux/* s1o9H */);
                if(!_Uy/* s1o9I */._){
                  return E(_Uw/* s1o9G */);
                }else{
                  var _Uz/*  s1o9G */ = B(_TH/* GHC.Integer.Type.plusInteger */(B(_U7/* GHC.Integer.Type.timesInteger */(_Uw/* s1o9G */, _Uq/* s1o9s */)), _Uy/* s1o9I */.a));
                  _Uw/* s1o9G */ = _Uz/*  s1o9G */;
                  _Ux/* s1o9H */ = _Uy/* s1o9I */.b;
                  continue;
                }
              }
            };
            return new F(function(){return _Uv/* s1o9F */(_Uk/* Text.Read.Lex.numberToFixed3 */, _Ut/* s1o9v */);});
          }else{
            var _UA/* s1o9N */ = B(_U7/* GHC.Integer.Type.timesInteger */(_Uq/* s1o9s */, _Uq/* s1o9s */));
            if(!(_Uu/* s1o9B */%2)){
              var _UB/*   s1o9u */ = B(_Uf/* Text.Read.Lex.combine */(_Uq/* s1o9s */, _Ut/* s1o9v */));
              _Um/*  s1o9s */ = _UA/* s1o9N */;
              _Un/*  s1o9t */ = quot/* EXTERNAL */(_Uu/* s1o9B */+1|0, 2);
              _Uo/*  s1o9u */ = _UB/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }else{
              var _UB/*   s1o9u */ = B(_Uf/* Text.Read.Lex.combine */(_Uq/* s1o9s */, new T2(1,_Uk/* Text.Read.Lex.numberToFixed3 */,_Ut/* s1o9v */)));
              _Um/*  s1o9s */ = _UA/* s1o9N */;
              _Un/*  s1o9t */ = quot/* EXTERNAL */(_Uu/* s1o9B */+1|0, 2);
              _Uo/*  s1o9u */ = _UB/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }
          }
        }
      }
    })(_Um/*  s1o9s */, _Un/*  s1o9t */, _Uo/*  s1o9u */));
    if(_Up/*  numberToFixed_go */!=__continue/* EXTERNAL */){
      return _Up/*  numberToFixed_go */;
    }
  }
},
_UC/* valInteger */ = function(_UD/* s1off */, _UE/* s1ofg */){
  return new F(function(){return _Ul/* Text.Read.Lex.numberToFixed_go */(_UD/* s1off */, new T(function(){
    return B(_TW/* GHC.List.$wlenAcc */(_UE/* s1ofg */, 0));
  },1), B(_2S/* GHC.Base.map */(_U3/* Text.Read.Lex.numberToFixed2 */, _UE/* s1ofg */)));});
},
_UF/* a26 */ = function(_UG/* s1og4 */){
  var _UH/* s1og5 */ = new T(function(){
    var _UI/* s1ogC */ = new T(function(){
      var _UJ/* s1ogz */ = function(_UK/* s1ogw */){
        return new F(function(){return A1(_UG/* s1og4 */,new T1(1,new T(function(){
          return B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _UK/* s1ogw */));
        })));});
      };
      return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_TE/* Text.Read.Lex.lvl */, _UJ/* s1ogz */)));
    }),
    _UL/* s1ogt */ = function(_UM/* s1ogj */){
      if(E(_UM/* s1ogj */)==43){
        var _UN/* s1ogq */ = function(_UO/* s1ogn */){
          return new F(function(){return A1(_UG/* s1og4 */,new T1(1,new T(function(){
            return B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _UO/* s1ogn */));
          })));});
        };
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_TE/* Text.Read.Lex.lvl */, _UN/* s1ogq */)));
      }else{
        return new T0(2);
      }
    },
    _UP/* s1ogh */ = function(_UQ/* s1og6 */){
      if(E(_UQ/* s1og6 */)==45){
        var _UR/* s1oge */ = function(_US/* s1oga */){
          return new F(function(){return A1(_UG/* s1og4 */,new T1(1,new T(function(){
            return B(_TR/* GHC.Integer.Type.negateInteger */(B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _US/* s1oga */))));
          })));});
        };
        return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_TE/* Text.Read.Lex.lvl */, _UR/* s1oge */)));
      }else{
        return new T0(2);
      }
    };
    return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_UP/* s1ogh */), new T1(0,_UL/* s1ogt */))), _UI/* s1ogC */));
  });
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_UT/* s1ogD */){
    return (E(_UT/* s1ogD */)==101) ? E(_UH/* s1og5 */) : new T0(2);
  }), new T1(0,function(_UU/* s1ogJ */){
    return (E(_UU/* s1ogJ */)==69) ? E(_UH/* s1og5 */) : new T0(2);
  }));});
},
_UV/* $wa8 */ = function(_UW/* s1odz */){
  var _UX/* s1odA */ = function(_UY/* s1odB */){
    return new F(function(){return A1(_UW/* s1odz */,new T1(1,_UY/* s1odB */));});
  };
  return function(_UZ/* s1odD */){
    return (E(_UZ/* s1odD */)==46) ? new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_TE/* Text.Read.Lex.lvl */, _UX/* s1odA */))) : new T0(2);
  };
},
_V0/* a3 */ = function(_V1/* s1odK */){
  return new T1(0,B(_UV/* Text.Read.Lex.$wa8 */(_V1/* s1odK */)));
},
_V2/* $wa10 */ = function(_V3/* s1ogP */){
  var _V4/* s1oh1 */ = function(_V5/* s1ogQ */){
    var _V6/* s1ogY */ = function(_V7/* s1ogR */){
      return new T1(1,B(_RW/* Text.ParserCombinators.ReadP.$wa */(_UF/* Text.Read.Lex.a26 */, _TA/* Text.Read.Lex.a */, function(_V8/* s1ogS */){
        return new F(function(){return A1(_V3/* s1ogP */,new T1(5,new T3(1,_V5/* s1ogQ */,_V7/* s1ogR */,_V8/* s1ogS */)));});
      })));
    };
    return new T1(1,B(_RW/* Text.ParserCombinators.ReadP.$wa */(_V0/* Text.Read.Lex.a3 */, _TC/* Text.Read.Lex.a1 */, _V6/* s1ogY */)));
  };
  return new F(function(){return _SD/* Text.Read.Lex.$wa6 */(_TE/* Text.Read.Lex.lvl */, _V4/* s1oh1 */);});
},
_V9/* a27 */ = function(_Va/* s1oh2 */){
  return new T1(1,B(_V2/* Text.Read.Lex.$wa10 */(_Va/* s1oh2 */)));
},
_Vb/* == */ = function(_Vc/* scBJ */){
  return E(E(_Vc/* scBJ */).a);
},
_Vd/* elem */ = function(_Ve/* s9uW */, _Vf/* s9uX */, _Vg/* s9uY */){
  while(1){
    var _Vh/* s9uZ */ = E(_Vg/* s9uY */);
    if(!_Vh/* s9uZ */._){
      return false;
    }else{
      if(!B(A3(_Vb/* GHC.Classes.== */,_Ve/* s9uW */, _Vf/* s9uX */, _Vh/* s9uZ */.a))){
        _Vg/* s9uY */ = _Vh/* s9uZ */.b;
        continue;
      }else{
        return true;
      }
    }
  }
},
_Vi/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!@#$%&*+./<=>?\\^|:-~"));
}),
_Vj/* a6 */ = function(_Vk/* s1odZ */){
  return new F(function(){return _Vd/* GHC.List.elem */(_Rs/* GHC.Classes.$fEqChar */, _Vk/* s1odZ */, _Vi/* Text.Read.Lex.lvl44 */);});
},
_Vl/* $wa9 */ = function(_Vm/* s1odN */){
  var _Vn/* s1odO */ = new T(function(){
    return B(A1(_Vm/* s1odN */,_To/* Text.Read.Lex.lvl42 */));
  }),
  _Vo/* s1odP */ = new T(function(){
    return B(A1(_Vm/* s1odN */,_Tn/* Text.Read.Lex.lvl41 */));
  });
  return function(_Vp/* s1odQ */){
    switch(E(_Vp/* s1odQ */)){
      case 79:
        return E(_Vn/* s1odO */);
      case 88:
        return E(_Vo/* s1odP */);
      case 111:
        return E(_Vn/* s1odO */);
      case 120:
        return E(_Vo/* s1odP */);
      default:
        return new T0(2);
    }
  };
},
_Vq/* a4 */ = function(_Vr/* s1odV */){
  return new T1(0,B(_Vl/* Text.Read.Lex.$wa9 */(_Vr/* s1odV */)));
},
_Vs/* a5 */ = function(_Vt/* s1odY */){
  return new F(function(){return A1(_Vt/* s1odY */,_TE/* Text.Read.Lex.lvl */);});
},
_Vu/* chr2 */ = function(_Vv/* sjTv */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Prelude.chr: bad argument: ", new T(function(){
    return B(_4e/* GHC.Show.$wshowSignedInt */(9, _Vv/* sjTv */, _I/* GHC.Types.[] */));
  }))));});
},
_Vw/* integerToInt */ = function(_Vx/* s1Rv */){
  var _Vy/* s1Rw */ = E(_Vx/* s1Rv */);
  if(!_Vy/* s1Rw */._){
    return E(_Vy/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_Vy/* s1Rw */.a);});
  }
},
_Vz/* leInteger */ = function(_VA/* s1Gp */, _VB/* s1Gq */){
  var _VC/* s1Gr */ = E(_VA/* s1Gp */);
  if(!_VC/* s1Gr */._){
    var _VD/* s1Gs */ = _VC/* s1Gr */.a,
    _VE/* s1Gt */ = E(_VB/* s1Gq */);
    return (_VE/* s1Gt */._==0) ? _VD/* s1Gs */<=_VE/* s1Gt */.a : I_compareInt/* EXTERNAL */(_VE/* s1Gt */.a, _VD/* s1Gs */)>=0;
  }else{
    var _VF/* s1GA */ = _VC/* s1Gr */.a,
    _VG/* s1GB */ = E(_VB/* s1Gq */);
    return (_VG/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_VF/* s1GA */, _VG/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_VF/* s1GA */, _VG/* s1GB */.a)<=0;
  }
},
_VH/* pfail1 */ = function(_VI/* s1izT */){
  return new T0(2);
},
_VJ/* choice */ = function(_VK/* s1iDZ */){
  var _VL/* s1iE0 */ = E(_VK/* s1iDZ */);
  if(!_VL/* s1iE0 */._){
    return E(_VH/* Text.ParserCombinators.ReadP.pfail1 */);
  }else{
    var _VM/* s1iE1 */ = _VL/* s1iE0 */.a,
    _VN/* s1iE3 */ = E(_VL/* s1iE0 */.b);
    if(!_VN/* s1iE3 */._){
      return E(_VM/* s1iE1 */);
    }else{
      var _VO/* s1iE6 */ = new T(function(){
        return B(_VJ/* Text.ParserCombinators.ReadP.choice */(_VN/* s1iE3 */));
      }),
      _VP/* s1iEa */ = function(_VQ/* s1iE7 */){
        return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_VM/* s1iE1 */,_VQ/* s1iE7 */)), new T(function(){
          return B(A1(_VO/* s1iE6 */,_VQ/* s1iE7 */));
        }));});
      };
      return E(_VP/* s1iEa */);
    }
  }
},
_VR/* $wa6 */ = function(_VS/* s1izU */, _VT/* s1izV */){
  var _VU/* s1izW */ = function(_VV/* s1izX */, _VW/* s1izY */, _VX/* s1izZ */){
    var _VY/* s1iA0 */ = E(_VV/* s1izX */);
    if(!_VY/* s1iA0 */._){
      return new F(function(){return A1(_VX/* s1izZ */,_VS/* s1izU */);});
    }else{
      var _VZ/* s1iA3 */ = E(_VW/* s1izY */);
      if(!_VZ/* s1iA3 */._){
        return new T0(2);
      }else{
        if(E(_VY/* s1iA0 */.a)!=E(_VZ/* s1iA3 */.a)){
          return new T0(2);
        }else{
          var _W0/* s1iAc */ = new T(function(){
            return B(_VU/* s1izW */(_VY/* s1iA0 */.b, _VZ/* s1iA3 */.b, _VX/* s1izZ */));
          });
          return new T1(0,function(_W1/* s1iAd */){
            return E(_W0/* s1iAc */);
          });
        }
      }
    }
  };
  return function(_W2/* s1iAf */){
    return new F(function(){return _VU/* s1izW */(_VS/* s1izU */, _W2/* s1iAf */, _VT/* s1izV */);});
  };
},
_W3/* a28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_W4/* lvl29 */ = 14,
_W5/* a29 */ = function(_W6/* s1onM */){
  var _W7/* s1onN */ = new T(function(){
    return B(A1(_W6/* s1onM */,_W4/* Text.Read.Lex.lvl29 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_W3/* Text.Read.Lex.a28 */, function(_W8/* s1onO */){
    return E(_W7/* s1onN */);
  })));
},
_W9/* a30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_Wa/* lvl35 */ = 1,
_Wb/* a31 */ = function(_Wc/* s1onS */){
  var _Wd/* s1onT */ = new T(function(){
    return B(A1(_Wc/* s1onS */,_Wa/* Text.Read.Lex.lvl35 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_W9/* Text.Read.Lex.a30 */, function(_We/* s1onU */){
    return E(_Wd/* s1onT */);
  })));
},
_Wf/* a32 */ = function(_Wg/* s1onY */){
  return new T1(1,B(_RW/* Text.ParserCombinators.ReadP.$wa */(_Wb/* Text.Read.Lex.a31 */, _W5/* Text.Read.Lex.a29 */, _Wg/* s1onY */)));
},
_Wh/* a33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_Wi/* lvl36 */ = 0,
_Wj/* a34 */ = function(_Wk/* s1oo1 */){
  var _Wl/* s1oo2 */ = new T(function(){
    return B(A1(_Wk/* s1oo1 */,_Wi/* Text.Read.Lex.lvl36 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Wh/* Text.Read.Lex.a33 */, function(_Wm/* s1oo3 */){
    return E(_Wl/* s1oo2 */);
  })));
},
_Wn/* a35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_Wo/* lvl34 */ = 2,
_Wp/* a36 */ = function(_Wq/* s1oo7 */){
  var _Wr/* s1oo8 */ = new T(function(){
    return B(A1(_Wq/* s1oo7 */,_Wo/* Text.Read.Lex.lvl34 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Wn/* Text.Read.Lex.a35 */, function(_Ws/* s1oo9 */){
    return E(_Wr/* s1oo8 */);
  })));
},
_Wt/* a37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_Wu/* lvl33 */ = 3,
_Wv/* a38 */ = function(_Ww/* s1ood */){
  var _Wx/* s1ooe */ = new T(function(){
    return B(A1(_Ww/* s1ood */,_Wu/* Text.Read.Lex.lvl33 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Wt/* Text.Read.Lex.a37 */, function(_Wy/* s1oof */){
    return E(_Wx/* s1ooe */);
  })));
},
_Wz/* a39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_WA/* lvl32 */ = 4,
_WB/* a40 */ = function(_WC/* s1ooj */){
  var _WD/* s1ook */ = new T(function(){
    return B(A1(_WC/* s1ooj */,_WA/* Text.Read.Lex.lvl32 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Wz/* Text.Read.Lex.a39 */, function(_WE/* s1ool */){
    return E(_WD/* s1ook */);
  })));
},
_WF/* a41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_WG/* lvl31 */ = 5,
_WH/* a42 */ = function(_WI/* s1oop */){
  var _WJ/* s1ooq */ = new T(function(){
    return B(A1(_WI/* s1oop */,_WG/* Text.Read.Lex.lvl31 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_WF/* Text.Read.Lex.a41 */, function(_WK/* s1oor */){
    return E(_WJ/* s1ooq */);
  })));
},
_WL/* a43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_WM/* lvl30 */ = 6,
_WN/* a44 */ = function(_WO/* s1oov */){
  var _WP/* s1oow */ = new T(function(){
    return B(A1(_WO/* s1oov */,_WM/* Text.Read.Lex.lvl30 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_WL/* Text.Read.Lex.a43 */, function(_WQ/* s1oox */){
    return E(_WP/* s1oow */);
  })));
},
_WR/* a45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_WS/* lvl7 */ = 7,
_WT/* a46 */ = function(_WU/* s1ooB */){
  var _WV/* s1ooC */ = new T(function(){
    return B(A1(_WU/* s1ooB */,_WS/* Text.Read.Lex.lvl7 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_WR/* Text.Read.Lex.a45 */, function(_WW/* s1ooD */){
    return E(_WV/* s1ooC */);
  })));
},
_WX/* a47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_WY/* lvl6 */ = 8,
_WZ/* a48 */ = function(_X0/* s1ooH */){
  var _X1/* s1ooI */ = new T(function(){
    return B(A1(_X0/* s1ooH */,_WY/* Text.Read.Lex.lvl6 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_WX/* Text.Read.Lex.a47 */, function(_X2/* s1ooJ */){
    return E(_X1/* s1ooI */);
  })));
},
_X3/* a49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_X4/* lvl2 */ = 9,
_X5/* a50 */ = function(_X6/* s1ooN */){
  var _X7/* s1ooO */ = new T(function(){
    return B(A1(_X6/* s1ooN */,_X4/* Text.Read.Lex.lvl2 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_X3/* Text.Read.Lex.a49 */, function(_X8/* s1ooP */){
    return E(_X7/* s1ooO */);
  })));
},
_X9/* a51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_Xa/* lvl4 */ = 10,
_Xb/* a52 */ = function(_Xc/* s1ooT */){
  var _Xd/* s1ooU */ = new T(function(){
    return B(A1(_Xc/* s1ooT */,_Xa/* Text.Read.Lex.lvl4 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_X9/* Text.Read.Lex.a51 */, function(_Xe/* s1ooV */){
    return E(_Xd/* s1ooU */);
  })));
},
_Xf/* a53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_Xg/* lvl1 */ = 11,
_Xh/* a54 */ = function(_Xi/* s1ooZ */){
  var _Xj/* s1op0 */ = new T(function(){
    return B(A1(_Xi/* s1ooZ */,_Xg/* Text.Read.Lex.lvl1 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Xf/* Text.Read.Lex.a53 */, function(_Xk/* s1op1 */){
    return E(_Xj/* s1op0 */);
  })));
},
_Xl/* a55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_Xm/* lvl5 */ = 12,
_Xn/* a56 */ = function(_Xo/* s1op5 */){
  var _Xp/* s1op6 */ = new T(function(){
    return B(A1(_Xo/* s1op5 */,_Xm/* Text.Read.Lex.lvl5 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Xl/* Text.Read.Lex.a55 */, function(_Xq/* s1op7 */){
    return E(_Xp/* s1op6 */);
  })));
},
_Xr/* a57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_Xs/* lvl3 */ = 13,
_Xt/* a58 */ = function(_Xu/* s1opb */){
  var _Xv/* s1opc */ = new T(function(){
    return B(A1(_Xu/* s1opb */,_Xs/* Text.Read.Lex.lvl3 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Xr/* Text.Read.Lex.a57 */, function(_Xw/* s1opd */){
    return E(_Xv/* s1opc */);
  })));
},
_Xx/* a59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_Xy/* lvl28 */ = 15,
_Xz/* a60 */ = function(_XA/* s1oph */){
  var _XB/* s1opi */ = new T(function(){
    return B(A1(_XA/* s1oph */,_Xy/* Text.Read.Lex.lvl28 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Xx/* Text.Read.Lex.a59 */, function(_XC/* s1opj */){
    return E(_XB/* s1opi */);
  })));
},
_XD/* a61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_XE/* lvl27 */ = 16,
_XF/* a62 */ = function(_XG/* s1opn */){
  var _XH/* s1opo */ = new T(function(){
    return B(A1(_XG/* s1opn */,_XE/* Text.Read.Lex.lvl27 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_XD/* Text.Read.Lex.a61 */, function(_XI/* s1opp */){
    return E(_XH/* s1opo */);
  })));
},
_XJ/* a63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_XK/* lvl26 */ = 17,
_XL/* a64 */ = function(_XM/* s1opt */){
  var _XN/* s1opu */ = new T(function(){
    return B(A1(_XM/* s1opt */,_XK/* Text.Read.Lex.lvl26 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_XJ/* Text.Read.Lex.a63 */, function(_XO/* s1opv */){
    return E(_XN/* s1opu */);
  })));
},
_XP/* a65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_XQ/* lvl25 */ = 18,
_XR/* a66 */ = function(_XS/* s1opz */){
  var _XT/* s1opA */ = new T(function(){
    return B(A1(_XS/* s1opz */,_XQ/* Text.Read.Lex.lvl25 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_XP/* Text.Read.Lex.a65 */, function(_XU/* s1opB */){
    return E(_XT/* s1opA */);
  })));
},
_XV/* a67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_XW/* lvl24 */ = 19,
_XX/* a68 */ = function(_XY/* s1opF */){
  var _XZ/* s1opG */ = new T(function(){
    return B(A1(_XY/* s1opF */,_XW/* Text.Read.Lex.lvl24 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_XV/* Text.Read.Lex.a67 */, function(_Y0/* s1opH */){
    return E(_XZ/* s1opG */);
  })));
},
_Y1/* a69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_Y2/* lvl23 */ = 20,
_Y3/* a70 */ = function(_Y4/* s1opL */){
  var _Y5/* s1opM */ = new T(function(){
    return B(A1(_Y4/* s1opL */,_Y2/* Text.Read.Lex.lvl23 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Y1/* Text.Read.Lex.a69 */, function(_Y6/* s1opN */){
    return E(_Y5/* s1opM */);
  })));
},
_Y7/* a71 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_Y8/* lvl22 */ = 21,
_Y9/* a72 */ = function(_Ya/* s1opR */){
  var _Yb/* s1opS */ = new T(function(){
    return B(A1(_Ya/* s1opR */,_Y8/* Text.Read.Lex.lvl22 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Y7/* Text.Read.Lex.a71 */, function(_Yc/* s1opT */){
    return E(_Yb/* s1opS */);
  })));
},
_Yd/* a73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_Ye/* lvl21 */ = 22,
_Yf/* a74 */ = function(_Yg/* s1opX */){
  var _Yh/* s1opY */ = new T(function(){
    return B(A1(_Yg/* s1opX */,_Ye/* Text.Read.Lex.lvl21 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Yd/* Text.Read.Lex.a73 */, function(_Yi/* s1opZ */){
    return E(_Yh/* s1opY */);
  })));
},
_Yj/* a75 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_Yk/* lvl20 */ = 23,
_Yl/* a76 */ = function(_Ym/* s1oq3 */){
  var _Yn/* s1oq4 */ = new T(function(){
    return B(A1(_Ym/* s1oq3 */,_Yk/* Text.Read.Lex.lvl20 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Yj/* Text.Read.Lex.a75 */, function(_Yo/* s1oq5 */){
    return E(_Yn/* s1oq4 */);
  })));
},
_Yp/* a77 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_Yq/* lvl19 */ = 24,
_Yr/* a78 */ = function(_Ys/* s1oq9 */){
  var _Yt/* s1oqa */ = new T(function(){
    return B(A1(_Ys/* s1oq9 */,_Yq/* Text.Read.Lex.lvl19 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Yp/* Text.Read.Lex.a77 */, function(_Yu/* s1oqb */){
    return E(_Yt/* s1oqa */);
  })));
},
_Yv/* a79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_Yw/* lvl18 */ = 25,
_Yx/* a80 */ = function(_Yy/* s1oqf */){
  var _Yz/* s1oqg */ = new T(function(){
    return B(A1(_Yy/* s1oqf */,_Yw/* Text.Read.Lex.lvl18 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Yv/* Text.Read.Lex.a79 */, function(_YA/* s1oqh */){
    return E(_Yz/* s1oqg */);
  })));
},
_YB/* a81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_YC/* lvl17 */ = 26,
_YD/* a82 */ = function(_YE/* s1oql */){
  var _YF/* s1oqm */ = new T(function(){
    return B(A1(_YE/* s1oql */,_YC/* Text.Read.Lex.lvl17 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_YB/* Text.Read.Lex.a81 */, function(_YG/* s1oqn */){
    return E(_YF/* s1oqm */);
  })));
},
_YH/* a83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_YI/* lvl16 */ = 27,
_YJ/* a84 */ = function(_YK/* s1oqr */){
  var _YL/* s1oqs */ = new T(function(){
    return B(A1(_YK/* s1oqr */,_YI/* Text.Read.Lex.lvl16 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_YH/* Text.Read.Lex.a83 */, function(_YM/* s1oqt */){
    return E(_YL/* s1oqs */);
  })));
},
_YN/* a85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_YO/* lvl15 */ = 28,
_YP/* a86 */ = function(_YQ/* s1oqx */){
  var _YR/* s1oqy */ = new T(function(){
    return B(A1(_YQ/* s1oqx */,_YO/* Text.Read.Lex.lvl15 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_YN/* Text.Read.Lex.a85 */, function(_YS/* s1oqz */){
    return E(_YR/* s1oqy */);
  })));
},
_YT/* a87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_YU/* lvl14 */ = 29,
_YV/* a88 */ = function(_YW/* s1oqD */){
  var _YX/* s1oqE */ = new T(function(){
    return B(A1(_YW/* s1oqD */,_YU/* Text.Read.Lex.lvl14 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_YT/* Text.Read.Lex.a87 */, function(_YY/* s1oqF */){
    return E(_YX/* s1oqE */);
  })));
},
_YZ/* a89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_Z0/* lvl13 */ = 30,
_Z1/* a90 */ = function(_Z2/* s1oqJ */){
  var _Z3/* s1oqK */ = new T(function(){
    return B(A1(_Z2/* s1oqJ */,_Z0/* Text.Read.Lex.lvl13 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_YZ/* Text.Read.Lex.a89 */, function(_Z4/* s1oqL */){
    return E(_Z3/* s1oqK */);
  })));
},
_Z5/* a91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_Z6/* lvl12 */ = 31,
_Z7/* a92 */ = function(_Z8/* s1oqP */){
  var _Z9/* s1oqQ */ = new T(function(){
    return B(A1(_Z8/* s1oqP */,_Z6/* Text.Read.Lex.lvl12 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Z5/* Text.Read.Lex.a91 */, function(_Za/* s1oqR */){
    return E(_Z9/* s1oqQ */);
  })));
},
_Zb/* a93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_Zc/* x */ = 32,
_Zd/* a94 */ = function(_Ze/* s1oqV */){
  var _Zf/* s1oqW */ = new T(function(){
    return B(A1(_Ze/* s1oqV */,_Zc/* Text.Read.Lex.x */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Zb/* Text.Read.Lex.a93 */, function(_Zg/* s1oqX */){
    return E(_Zf/* s1oqW */);
  })));
},
_Zh/* a95 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DEL"));
}),
_Zi/* x1 */ = 127,
_Zj/* a96 */ = function(_Zk/* s1or1 */){
  var _Zl/* s1or2 */ = new T(function(){
    return B(A1(_Zk/* s1or1 */,_Zi/* Text.Read.Lex.x1 */));
  });
  return new T1(1,B(_VR/* Text.ParserCombinators.ReadP.$wa6 */(_Zh/* Text.Read.Lex.a95 */, function(_Zm/* s1or3 */){
    return E(_Zl/* s1or2 */);
  })));
},
_Zn/* lvl47 */ = new T2(1,_Zj/* Text.Read.Lex.a96 */,_I/* GHC.Types.[] */),
_Zo/* lvl48 */ = new T2(1,_Zd/* Text.Read.Lex.a94 */,_Zn/* Text.Read.Lex.lvl47 */),
_Zp/* lvl49 */ = new T2(1,_Z7/* Text.Read.Lex.a92 */,_Zo/* Text.Read.Lex.lvl48 */),
_Zq/* lvl50 */ = new T2(1,_Z1/* Text.Read.Lex.a90 */,_Zp/* Text.Read.Lex.lvl49 */),
_Zr/* lvl51 */ = new T2(1,_YV/* Text.Read.Lex.a88 */,_Zq/* Text.Read.Lex.lvl50 */),
_Zs/* lvl52 */ = new T2(1,_YP/* Text.Read.Lex.a86 */,_Zr/* Text.Read.Lex.lvl51 */),
_Zt/* lvl53 */ = new T2(1,_YJ/* Text.Read.Lex.a84 */,_Zs/* Text.Read.Lex.lvl52 */),
_Zu/* lvl54 */ = new T2(1,_YD/* Text.Read.Lex.a82 */,_Zt/* Text.Read.Lex.lvl53 */),
_Zv/* lvl55 */ = new T2(1,_Yx/* Text.Read.Lex.a80 */,_Zu/* Text.Read.Lex.lvl54 */),
_Zw/* lvl56 */ = new T2(1,_Yr/* Text.Read.Lex.a78 */,_Zv/* Text.Read.Lex.lvl55 */),
_Zx/* lvl57 */ = new T2(1,_Yl/* Text.Read.Lex.a76 */,_Zw/* Text.Read.Lex.lvl56 */),
_Zy/* lvl58 */ = new T2(1,_Yf/* Text.Read.Lex.a74 */,_Zx/* Text.Read.Lex.lvl57 */),
_Zz/* lvl59 */ = new T2(1,_Y9/* Text.Read.Lex.a72 */,_Zy/* Text.Read.Lex.lvl58 */),
_ZA/* lvl60 */ = new T2(1,_Y3/* Text.Read.Lex.a70 */,_Zz/* Text.Read.Lex.lvl59 */),
_ZB/* lvl61 */ = new T2(1,_XX/* Text.Read.Lex.a68 */,_ZA/* Text.Read.Lex.lvl60 */),
_ZC/* lvl62 */ = new T2(1,_XR/* Text.Read.Lex.a66 */,_ZB/* Text.Read.Lex.lvl61 */),
_ZD/* lvl63 */ = new T2(1,_XL/* Text.Read.Lex.a64 */,_ZC/* Text.Read.Lex.lvl62 */),
_ZE/* lvl64 */ = new T2(1,_XF/* Text.Read.Lex.a62 */,_ZD/* Text.Read.Lex.lvl63 */),
_ZF/* lvl65 */ = new T2(1,_Xz/* Text.Read.Lex.a60 */,_ZE/* Text.Read.Lex.lvl64 */),
_ZG/* lvl66 */ = new T2(1,_Xt/* Text.Read.Lex.a58 */,_ZF/* Text.Read.Lex.lvl65 */),
_ZH/* lvl67 */ = new T2(1,_Xn/* Text.Read.Lex.a56 */,_ZG/* Text.Read.Lex.lvl66 */),
_ZI/* lvl68 */ = new T2(1,_Xh/* Text.Read.Lex.a54 */,_ZH/* Text.Read.Lex.lvl67 */),
_ZJ/* lvl69 */ = new T2(1,_Xb/* Text.Read.Lex.a52 */,_ZI/* Text.Read.Lex.lvl68 */),
_ZK/* lvl70 */ = new T2(1,_X5/* Text.Read.Lex.a50 */,_ZJ/* Text.Read.Lex.lvl69 */),
_ZL/* lvl71 */ = new T2(1,_WZ/* Text.Read.Lex.a48 */,_ZK/* Text.Read.Lex.lvl70 */),
_ZM/* lvl72 */ = new T2(1,_WT/* Text.Read.Lex.a46 */,_ZL/* Text.Read.Lex.lvl71 */),
_ZN/* lvl73 */ = new T2(1,_WN/* Text.Read.Lex.a44 */,_ZM/* Text.Read.Lex.lvl72 */),
_ZO/* lvl74 */ = new T2(1,_WH/* Text.Read.Lex.a42 */,_ZN/* Text.Read.Lex.lvl73 */),
_ZP/* lvl75 */ = new T2(1,_WB/* Text.Read.Lex.a40 */,_ZO/* Text.Read.Lex.lvl74 */),
_ZQ/* lvl76 */ = new T2(1,_Wv/* Text.Read.Lex.a38 */,_ZP/* Text.Read.Lex.lvl75 */),
_ZR/* lvl77 */ = new T2(1,_Wp/* Text.Read.Lex.a36 */,_ZQ/* Text.Read.Lex.lvl76 */),
_ZS/* lvl78 */ = new T2(1,_Wj/* Text.Read.Lex.a34 */,_ZR/* Text.Read.Lex.lvl77 */),
_ZT/* lvl79 */ = new T2(1,_Wf/* Text.Read.Lex.a32 */,_ZS/* Text.Read.Lex.lvl78 */),
_ZU/* lexAscii */ = new T(function(){
  return B(_VJ/* Text.ParserCombinators.ReadP.choice */(_ZT/* Text.Read.Lex.lvl79 */));
}),
_ZV/* lvl10 */ = 34,
_ZW/* lvl11 */ = new T1(0,1114111),
_ZX/* lvl8 */ = 92,
_ZY/* lvl9 */ = 39,
_ZZ/* lexChar2 */ = function(_100/* s1or7 */){
  var _101/* s1or8 */ = new T(function(){
    return B(A1(_100/* s1or7 */,_WS/* Text.Read.Lex.lvl7 */));
  }),
  _102/* s1or9 */ = new T(function(){
    return B(A1(_100/* s1or7 */,_WY/* Text.Read.Lex.lvl6 */));
  }),
  _103/* s1ora */ = new T(function(){
    return B(A1(_100/* s1or7 */,_X4/* Text.Read.Lex.lvl2 */));
  }),
  _104/* s1orb */ = new T(function(){
    return B(A1(_100/* s1or7 */,_Xa/* Text.Read.Lex.lvl4 */));
  }),
  _105/* s1orc */ = new T(function(){
    return B(A1(_100/* s1or7 */,_Xg/* Text.Read.Lex.lvl1 */));
  }),
  _106/* s1ord */ = new T(function(){
    return B(A1(_100/* s1or7 */,_Xm/* Text.Read.Lex.lvl5 */));
  }),
  _107/* s1ore */ = new T(function(){
    return B(A1(_100/* s1or7 */,_Xs/* Text.Read.Lex.lvl3 */));
  }),
  _108/* s1orf */ = new T(function(){
    return B(A1(_100/* s1or7 */,_ZX/* Text.Read.Lex.lvl8 */));
  }),
  _109/* s1org */ = new T(function(){
    return B(A1(_100/* s1or7 */,_ZY/* Text.Read.Lex.lvl9 */));
  }),
  _10a/* s1orh */ = new T(function(){
    return B(A1(_100/* s1or7 */,_ZV/* Text.Read.Lex.lvl10 */));
  }),
  _10b/* s1osl */ = new T(function(){
    var _10c/* s1orE */ = function(_10d/* s1oro */){
      var _10e/* s1orp */ = new T(function(){
        return B(_U1/* GHC.Integer.Type.smallInteger */(E(_10d/* s1oro */)));
      }),
      _10f/* s1orB */ = function(_10g/* s1ors */){
        var _10h/* s1ort */ = B(_UC/* Text.Read.Lex.valInteger */(_10e/* s1orp */, _10g/* s1ors */));
        if(!B(_Vz/* GHC.Integer.Type.leInteger */(_10h/* s1ort */, _ZW/* Text.Read.Lex.lvl11 */))){
          return new T0(2);
        }else{
          return new F(function(){return A1(_100/* s1or7 */,new T(function(){
            var _10i/* s1orv */ = B(_Vw/* GHC.Integer.Type.integerToInt */(_10h/* s1ort */));
            if(_10i/* s1orv */>>>0>1114111){
              return B(_Vu/* GHC.Char.chr2 */(_10i/* s1orv */));
            }else{
              return _10i/* s1orv */;
            }
          }));});
        }
      };
      return new T1(1,B(_SD/* Text.Read.Lex.$wa6 */(_10d/* s1oro */, _10f/* s1orB */)));
    },
    _10j/* s1osk */ = new T(function(){
      var _10k/* s1orI */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Z6/* Text.Read.Lex.lvl12 */));
      }),
      _10l/* s1orJ */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Z0/* Text.Read.Lex.lvl13 */));
      }),
      _10m/* s1orK */ = new T(function(){
        return B(A1(_100/* s1or7 */,_YU/* Text.Read.Lex.lvl14 */));
      }),
      _10n/* s1orL */ = new T(function(){
        return B(A1(_100/* s1or7 */,_YO/* Text.Read.Lex.lvl15 */));
      }),
      _10o/* s1orM */ = new T(function(){
        return B(A1(_100/* s1or7 */,_YI/* Text.Read.Lex.lvl16 */));
      }),
      _10p/* s1orN */ = new T(function(){
        return B(A1(_100/* s1or7 */,_YC/* Text.Read.Lex.lvl17 */));
      }),
      _10q/* s1orO */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Yw/* Text.Read.Lex.lvl18 */));
      }),
      _10r/* s1orP */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Yq/* Text.Read.Lex.lvl19 */));
      }),
      _10s/* s1orQ */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Yk/* Text.Read.Lex.lvl20 */));
      }),
      _10t/* s1orR */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Ye/* Text.Read.Lex.lvl21 */));
      }),
      _10u/* s1orS */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Y8/* Text.Read.Lex.lvl22 */));
      }),
      _10v/* s1orT */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Y2/* Text.Read.Lex.lvl23 */));
      }),
      _10w/* s1orU */ = new T(function(){
        return B(A1(_100/* s1or7 */,_XW/* Text.Read.Lex.lvl24 */));
      }),
      _10x/* s1orV */ = new T(function(){
        return B(A1(_100/* s1or7 */,_XQ/* Text.Read.Lex.lvl25 */));
      }),
      _10y/* s1orW */ = new T(function(){
        return B(A1(_100/* s1or7 */,_XK/* Text.Read.Lex.lvl26 */));
      }),
      _10z/* s1orX */ = new T(function(){
        return B(A1(_100/* s1or7 */,_XE/* Text.Read.Lex.lvl27 */));
      }),
      _10A/* s1orY */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Xy/* Text.Read.Lex.lvl28 */));
      }),
      _10B/* s1orZ */ = new T(function(){
        return B(A1(_100/* s1or7 */,_W4/* Text.Read.Lex.lvl29 */));
      }),
      _10C/* s1os0 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_WM/* Text.Read.Lex.lvl30 */));
      }),
      _10D/* s1os1 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_WG/* Text.Read.Lex.lvl31 */));
      }),
      _10E/* s1os2 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_WA/* Text.Read.Lex.lvl32 */));
      }),
      _10F/* s1os3 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Wu/* Text.Read.Lex.lvl33 */));
      }),
      _10G/* s1os4 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Wo/* Text.Read.Lex.lvl34 */));
      }),
      _10H/* s1os5 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Wa/* Text.Read.Lex.lvl35 */));
      }),
      _10I/* s1os6 */ = new T(function(){
        return B(A1(_100/* s1or7 */,_Wi/* Text.Read.Lex.lvl36 */));
      }),
      _10J/* s1os7 */ = function(_10K/* s1os8 */){
        switch(E(_10K/* s1os8 */)){
          case 64:
            return E(_10I/* s1os6 */);
          case 65:
            return E(_10H/* s1os5 */);
          case 66:
            return E(_10G/* s1os4 */);
          case 67:
            return E(_10F/* s1os3 */);
          case 68:
            return E(_10E/* s1os2 */);
          case 69:
            return E(_10D/* s1os1 */);
          case 70:
            return E(_10C/* s1os0 */);
          case 71:
            return E(_101/* s1or8 */);
          case 72:
            return E(_102/* s1or9 */);
          case 73:
            return E(_103/* s1ora */);
          case 74:
            return E(_104/* s1orb */);
          case 75:
            return E(_105/* s1orc */);
          case 76:
            return E(_106/* s1ord */);
          case 77:
            return E(_107/* s1ore */);
          case 78:
            return E(_10B/* s1orZ */);
          case 79:
            return E(_10A/* s1orY */);
          case 80:
            return E(_10z/* s1orX */);
          case 81:
            return E(_10y/* s1orW */);
          case 82:
            return E(_10x/* s1orV */);
          case 83:
            return E(_10w/* s1orU */);
          case 84:
            return E(_10v/* s1orT */);
          case 85:
            return E(_10u/* s1orS */);
          case 86:
            return E(_10t/* s1orR */);
          case 87:
            return E(_10s/* s1orQ */);
          case 88:
            return E(_10r/* s1orP */);
          case 89:
            return E(_10q/* s1orO */);
          case 90:
            return E(_10p/* s1orN */);
          case 91:
            return E(_10o/* s1orM */);
          case 92:
            return E(_10n/* s1orL */);
          case 93:
            return E(_10m/* s1orK */);
          case 94:
            return E(_10l/* s1orJ */);
          case 95:
            return E(_10k/* s1orI */);
          default:
            return new T0(2);
        }
      };
      return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_10L/* s1osd */){
        return (E(_10L/* s1osd */)==94) ? E(new T1(0,_10J/* s1os7 */)) : new T0(2);
      }), new T(function(){
        return B(A1(_ZU/* Text.Read.Lex.lexAscii */,_100/* s1or7 */));
      })));
    });
    return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_RW/* Text.ParserCombinators.ReadP.$wa */(_Vq/* Text.Read.Lex.a4 */, _Vs/* Text.Read.Lex.a5 */, _10c/* s1orE */))), _10j/* s1osk */));
  });
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_10M/* s1ori */){
    switch(E(_10M/* s1ori */)){
      case 34:
        return E(_10a/* s1orh */);
      case 39:
        return E(_109/* s1org */);
      case 92:
        return E(_108/* s1orf */);
      case 97:
        return E(_101/* s1or8 */);
      case 98:
        return E(_102/* s1or9 */);
      case 102:
        return E(_106/* s1ord */);
      case 110:
        return E(_104/* s1orb */);
      case 114:
        return E(_107/* s1ore */);
      case 116:
        return E(_103/* s1ora */);
      case 118:
        return E(_105/* s1orc */);
      default:
        return new T0(2);
    }
  }), _10b/* s1osl */);});
},
_10N/* a */ = function(_10O/* s1iyn */){
  return new F(function(){return A1(_10O/* s1iyn */,_0/* GHC.Tuple.() */);});
},
_10P/* skipSpaces_skip */ = function(_10Q/* s1iIB */){
  var _10R/* s1iIC */ = E(_10Q/* s1iIB */);
  if(!_10R/* s1iIC */._){
    return E(_10N/* Text.ParserCombinators.ReadP.a */);
  }else{
    var _10S/* s1iIF */ = E(_10R/* s1iIC */.a),
    _10T/* s1iIH */ = _10S/* s1iIF */>>>0,
    _10U/* s1iIJ */ = new T(function(){
      return B(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */(_10R/* s1iIC */.b));
    });
    if(_10T/* s1iIH */>887){
      var _10V/* s1iIO */ = u_iswspace/* EXTERNAL */(_10S/* s1iIF */);
      if(!E(_10V/* s1iIO */)){
        return E(_10N/* Text.ParserCombinators.ReadP.a */);
      }else{
        var _10W/* s1iIW */ = function(_10X/* s1iIS */){
          var _10Y/* s1iIT */ = new T(function(){
            return B(A1(_10U/* s1iIJ */,_10X/* s1iIS */));
          });
          return new T1(0,function(_10Z/* s1iIU */){
            return E(_10Y/* s1iIT */);
          });
        };
        return E(_10W/* s1iIW */);
      }
    }else{
      var _110/* s1iIX */ = E(_10T/* s1iIH */);
      if(_110/* s1iIX */==32){
        var _111/* s1iJg */ = function(_112/* s1iJc */){
          var _113/* s1iJd */ = new T(function(){
            return B(A1(_10U/* s1iIJ */,_112/* s1iJc */));
          });
          return new T1(0,function(_114/* s1iJe */){
            return E(_113/* s1iJd */);
          });
        };
        return E(_111/* s1iJg */);
      }else{
        if(_110/* s1iIX */-9>>>0>4){
          if(E(_110/* s1iIX */)==160){
            var _115/* s1iJ6 */ = function(_116/* s1iJ2 */){
              var _117/* s1iJ3 */ = new T(function(){
                return B(A1(_10U/* s1iIJ */,_116/* s1iJ2 */));
              });
              return new T1(0,function(_118/* s1iJ4 */){
                return E(_117/* s1iJ3 */);
              });
            };
            return E(_115/* s1iJ6 */);
          }else{
            return E(_10N/* Text.ParserCombinators.ReadP.a */);
          }
        }else{
          var _119/* s1iJb */ = function(_11a/* s1iJ7 */){
            var _11b/* s1iJ8 */ = new T(function(){
              return B(A1(_10U/* s1iIJ */,_11a/* s1iJ7 */));
            });
            return new T1(0,function(_11c/* s1iJ9 */){
              return E(_11b/* s1iJ8 */);
            });
          };
          return E(_119/* s1iJb */);
        }
      }
    }
  }
},
_11d/* a97 */ = function(_11e/* s1osm */){
  var _11f/* s1osn */ = new T(function(){
    return B(_11d/* Text.Read.Lex.a97 */(_11e/* s1osm */));
  }),
  _11g/* s1oso */ = function(_11h/* s1osp */){
    return (E(_11h/* s1osp */)==92) ? E(_11f/* s1osn */) : new T0(2);
  },
  _11i/* s1osu */ = function(_11j/* s1osv */){
    return E(new T1(0,_11g/* s1oso */));
  },
  _11k/* s1osy */ = new T1(1,function(_11l/* s1osx */){
    return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_11l/* s1osx */, _11i/* s1osu */);});
  }),
  _11m/* s1osz */ = new T(function(){
    return B(_ZZ/* Text.Read.Lex.lexChar2 */(function(_11n/* s1osA */){
      return new F(function(){return A1(_11e/* s1osm */,new T2(0,_11n/* s1osA */,_8n/* GHC.Types.True */));});
    }));
  }),
  _11o/* s1osD */ = function(_11p/* s1osE */){
    var _11q/* s1osH */ = E(_11p/* s1osE */);
    if(_11q/* s1osH */==38){
      return E(_11f/* s1osn */);
    }else{
      var _11r/* s1osI */ = _11q/* s1osH */>>>0;
      if(_11r/* s1osI */>887){
        var _11s/* s1osO */ = u_iswspace/* EXTERNAL */(_11q/* s1osH */);
        return (E(_11s/* s1osO */)==0) ? new T0(2) : E(_11k/* s1osy */);
      }else{
        var _11t/* s1osS */ = E(_11r/* s1osI */);
        return (_11t/* s1osS */==32) ? E(_11k/* s1osy */) : (_11t/* s1osS */-9>>>0>4) ? (E(_11t/* s1osS */)==160) ? E(_11k/* s1osy */) : new T0(2) : E(_11k/* s1osy */);
      }
    }
  };
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11u/* s1osY */){
    return (E(_11u/* s1osY */)==92) ? E(new T1(0,_11o/* s1osD */)) : new T0(2);
  }), new T1(0,function(_11v/* s1ot4 */){
    var _11w/* s1ot5 */ = E(_11v/* s1ot4 */);
    if(E(_11w/* s1ot5 */)==92){
      return E(_11m/* s1osz */);
    }else{
      return new F(function(){return A1(_11e/* s1osm */,new T2(0,_11w/* s1ot5 */,_2G/* GHC.Types.False */));});
    }
  }));});
},
_11x/* a98 */ = function(_11y/* s1otb */, _11z/* s1otc */){
  var _11A/* s1otd */ = new T(function(){
    return B(A1(_11z/* s1otc */,new T1(1,new T(function(){
      return B(A1(_11y/* s1otb */,_I/* GHC.Types.[] */));
    }))));
  }),
  _11B/* s1otu */ = function(_11C/* s1otg */){
    var _11D/* s1oth */ = E(_11C/* s1otg */),
    _11E/* s1otk */ = E(_11D/* s1oth */.a);
    if(E(_11E/* s1otk */)==34){
      if(!E(_11D/* s1oth */.b)){
        return E(_11A/* s1otd */);
      }else{
        return new F(function(){return _11x/* Text.Read.Lex.a98 */(function(_11F/* s1otr */){
          return new F(function(){return A1(_11y/* s1otb */,new T2(1,_11E/* s1otk */,_11F/* s1otr */));});
        }, _11z/* s1otc */);});
      }
    }else{
      return new F(function(){return _11x/* Text.Read.Lex.a98 */(function(_11G/* s1otn */){
        return new F(function(){return A1(_11y/* s1otb */,new T2(1,_11E/* s1otk */,_11G/* s1otn */));});
      }, _11z/* s1otc */);});
    }
  };
  return new F(function(){return _11d/* Text.Read.Lex.a97 */(_11B/* s1otu */);});
},
_11H/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_\'"));
}),
_11I/* $wisIdfChar */ = function(_11J/* s1otE */){
  var _11K/* s1otH */ = u_iswalnum/* EXTERNAL */(_11J/* s1otE */);
  if(!E(_11K/* s1otH */)){
    return new F(function(){return _Vd/* GHC.List.elem */(_Rs/* GHC.Classes.$fEqChar */, _11J/* s1otE */, _11H/* Text.Read.Lex.lvl45 */);});
  }else{
    return true;
  }
},
_11L/* isIdfChar */ = function(_11M/* s1otM */){
  return new F(function(){return _11I/* Text.Read.Lex.$wisIdfChar */(E(_11M/* s1otM */));});
},
_11N/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(",;()[]{}`"));
}),
_11O/* a7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("=>"));
}),
_11P/* a8 */ = new T2(1,_11O/* Text.Read.Lex.a7 */,_I/* GHC.Types.[] */),
_11Q/* a9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("~"));
}),
_11R/* a10 */ = new T2(1,_11Q/* Text.Read.Lex.a9 */,_11P/* Text.Read.Lex.a8 */),
_11S/* a11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("@"));
}),
_11T/* a12 */ = new T2(1,_11S/* Text.Read.Lex.a11 */,_11R/* Text.Read.Lex.a10 */),
_11U/* a13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("->"));
}),
_11V/* a14 */ = new T2(1,_11U/* Text.Read.Lex.a13 */,_11T/* Text.Read.Lex.a12 */),
_11W/* a15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<-"));
}),
_11X/* a16 */ = new T2(1,_11W/* Text.Read.Lex.a15 */,_11V/* Text.Read.Lex.a14 */),
_11Y/* a17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("|"));
}),
_11Z/* a18 */ = new T2(1,_11Y/* Text.Read.Lex.a17 */,_11X/* Text.Read.Lex.a16 */),
_120/* a19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\"));
}),
_121/* a20 */ = new T2(1,_120/* Text.Read.Lex.a19 */,_11Z/* Text.Read.Lex.a18 */),
_122/* a21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_123/* a22 */ = new T2(1,_122/* Text.Read.Lex.a21 */,_121/* Text.Read.Lex.a20 */),
_124/* a23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("::"));
}),
_125/* a24 */ = new T2(1,_124/* Text.Read.Lex.a23 */,_123/* Text.Read.Lex.a22 */),
_126/* a25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".."));
}),
_127/* reserved_ops */ = new T2(1,_126/* Text.Read.Lex.a25 */,_125/* Text.Read.Lex.a24 */),
_128/* expect2 */ = function(_129/* s1otP */){
  var _12a/* s1otQ */ = new T(function(){
    return B(A1(_129/* s1otP */,_SA/* Text.Read.Lex.EOF */));
  }),
  _12b/* s1ovk */ = new T(function(){
    var _12c/* s1otX */ = new T(function(){
      var _12d/* s1ou6 */ = function(_12e/* s1otY */){
        var _12f/* s1otZ */ = new T(function(){
          return B(A1(_129/* s1otP */,new T1(0,_12e/* s1otY */)));
        });
        return new T1(0,function(_12g/* s1ou1 */){
          return (E(_12g/* s1ou1 */)==39) ? E(_12f/* s1otZ */) : new T0(2);
        });
      };
      return B(_ZZ/* Text.Read.Lex.lexChar2 */(_12d/* s1ou6 */));
    }),
    _12h/* s1ou7 */ = function(_12i/* s1ou8 */){
      var _12j/* s1ou9 */ = E(_12i/* s1ou8 */);
      switch(E(_12j/* s1ou9 */)){
        case 39:
          return new T0(2);
        case 92:
          return E(_12c/* s1otX */);
        default:
          var _12k/* s1ouc */ = new T(function(){
            return B(A1(_129/* s1otP */,new T1(0,_12j/* s1ou9 */)));
          });
          return new T1(0,function(_12l/* s1oue */){
            return (E(_12l/* s1oue */)==39) ? E(_12k/* s1ouc */) : new T0(2);
          });
      }
    },
    _12m/* s1ovj */ = new T(function(){
      var _12n/* s1ouq */ = new T(function(){
        return B(_11x/* Text.Read.Lex.a98 */(_4/* GHC.Base.id */, _129/* s1otP */));
      }),
      _12o/* s1ovi */ = new T(function(){
        var _12p/* s1ovh */ = new T(function(){
          var _12q/* s1ovg */ = new T(function(){
            var _12r/* s1ovb */ = function(_12s/* s1ouP */){
              var _12t/* s1ouQ */ = E(_12s/* s1ouP */),
              _12u/* s1ouU */ = u_iswalpha/* EXTERNAL */(_12t/* s1ouQ */);
              return (E(_12u/* s1ouU */)==0) ? (E(_12t/* s1ouQ */)==95) ? new T1(1,B(_Sm/* Text.ParserCombinators.ReadP.$wa3 */(_11L/* Text.Read.Lex.isIdfChar */, function(_12v/* s1ov5 */){
                return new F(function(){return A1(_129/* s1otP */,new T1(3,new T2(1,_12t/* s1ouQ */,_12v/* s1ov5 */)));});
              }))) : new T0(2) : new T1(1,B(_Sm/* Text.ParserCombinators.ReadP.$wa3 */(_11L/* Text.Read.Lex.isIdfChar */, function(_12w/* s1ouY */){
                return new F(function(){return A1(_129/* s1otP */,new T1(3,new T2(1,_12t/* s1ouQ */,_12w/* s1ouY */)));});
              })));
            };
            return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_12r/* s1ovb */), new T(function(){
              return new T1(1,B(_RW/* Text.ParserCombinators.ReadP.$wa */(_Ty/* Text.Read.Lex.a2 */, _V9/* Text.Read.Lex.a27 */, _129/* s1otP */)));
            })));
          }),
          _12x/* s1ouN */ = function(_12y/* s1ouD */){
            return (!B(_Vd/* GHC.List.elem */(_Rs/* GHC.Classes.$fEqChar */, _12y/* s1ouD */, _Vi/* Text.Read.Lex.lvl44 */))) ? new T0(2) : new T1(1,B(_Sm/* Text.ParserCombinators.ReadP.$wa3 */(_Vj/* Text.Read.Lex.a6 */, function(_12z/* s1ouF */){
              var _12A/* s1ouG */ = new T2(1,_12y/* s1ouD */,_12z/* s1ouF */);
              if(!B(_Vd/* GHC.List.elem */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, _12A/* s1ouG */, _127/* Text.Read.Lex.reserved_ops */))){
                return new F(function(){return A1(_129/* s1otP */,new T1(4,_12A/* s1ouG */));});
              }else{
                return new F(function(){return A1(_129/* s1otP */,new T1(2,_12A/* s1ouG */));});
              }
            })));
          };
          return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_12x/* s1ouN */), _12q/* s1ovg */));
        });
        return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_12B/* s1oux */){
          if(!B(_Vd/* GHC.List.elem */(_Rs/* GHC.Classes.$fEqChar */, _12B/* s1oux */, _11N/* Text.Read.Lex.lvl43 */))){
            return new T0(2);
          }else{
            return new F(function(){return A1(_129/* s1otP */,new T1(2,new T2(1,_12B/* s1oux */,_I/* GHC.Types.[] */)));});
          }
        }), _12p/* s1ovh */));
      });
      return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_12C/* s1our */){
        return (E(_12C/* s1our */)==34) ? E(_12n/* s1ouq */) : new T0(2);
      }), _12o/* s1ovi */));
    });
    return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_12D/* s1ouk */){
      return (E(_12D/* s1ouk */)==39) ? E(new T1(0,_12h/* s1ou7 */)) : new T0(2);
    }), _12m/* s1ovj */));
  });
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_12E/* s1otR */){
    return (E(_12E/* s1otR */)._==0) ? E(_12a/* s1otQ */) : new T0(2);
  }), _12b/* s1ovk */);});
},
_12F/* minPrec */ = 0,
_12G/* $wa3 */ = function(_12H/* s1viS */, _12I/* s1viT */){
  var _12J/* s1viU */ = new T(function(){
    var _12K/* s1viV */ = new T(function(){
      var _12L/* s1vj8 */ = function(_12M/* s1viW */){
        var _12N/* s1viX */ = new T(function(){
          var _12O/* s1viY */ = new T(function(){
            return B(A1(_12I/* s1viT */,_12M/* s1viW */));
          });
          return B(_128/* Text.Read.Lex.expect2 */(function(_12P/* s1viZ */){
            var _12Q/* s1vj0 */ = E(_12P/* s1viZ */);
            return (_12Q/* s1vj0 */._==2) ? (!B(_J9/* GHC.Base.eqString */(_12Q/* s1vj0 */.a, _Rl/* GHC.Read.$fRead(,)4 */))) ? new T0(2) : E(_12O/* s1viY */) : new T0(2);
          }));
        }),
        _12R/* s1vj4 */ = function(_12S/* s1vj5 */){
          return E(_12N/* s1viX */);
        };
        return new T1(1,function(_12T/* s1vj6 */){
          return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12T/* s1vj6 */, _12R/* s1vj4 */);});
        });
      };
      return B(A2(_12H/* s1viS */,_12F/* Text.ParserCombinators.ReadPrec.minPrec */, _12L/* s1vj8 */));
    });
    return B(_128/* Text.Read.Lex.expect2 */(function(_12U/* s1vj9 */){
      var _12V/* s1vja */ = E(_12U/* s1vj9 */);
      return (_12V/* s1vja */._==2) ? (!B(_J9/* GHC.Base.eqString */(_12V/* s1vja */.a, _Rk/* GHC.Read.$fRead(,)3 */))) ? new T0(2) : E(_12K/* s1viV */) : new T0(2);
    }));
  }),
  _12W/* s1vje */ = function(_12X/* s1vjf */){
    return E(_12J/* s1viU */);
  };
  return function(_12Y/* s1vjg */){
    return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12Y/* s1vjg */, _12W/* s1vje */);});
  };
},
_12Z/* $fReadDouble10 */ = function(_130/* s1vjn */, _131/* s1vjo */){
  var _132/* s1vjp */ = function(_133/* s1vjq */){
    var _134/* s1vjr */ = new T(function(){
      return B(A1(_130/* s1vjn */,_133/* s1vjq */));
    }),
    _135/* s1vjx */ = function(_136/* s1vjs */){
      return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_134/* s1vjr */,_136/* s1vjs */)), new T(function(){
        return new T1(1,B(_12G/* GHC.Read.$wa3 */(_132/* s1vjp */, _136/* s1vjs */)));
      }));});
    };
    return E(_135/* s1vjx */);
  },
  _137/* s1vjy */ = new T(function(){
    return B(A1(_130/* s1vjn */,_131/* s1vjo */));
  }),
  _138/* s1vjE */ = function(_139/* s1vjz */){
    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_137/* s1vjy */,_139/* s1vjz */)), new T(function(){
      return new T1(1,B(_12G/* GHC.Read.$wa3 */(_132/* s1vjp */, _139/* s1vjz */)));
    }));});
  };
  return E(_138/* s1vjE */);
},
_13a/* $fReadFloat7 */ = function(_13b/* s1vli */, _13c/* s1vlj */){
  var _13d/* s1vlS */ = function(_13e/* s1vlk */, _13f/* s1vll */){
    var _13g/* s1vlm */ = function(_13h/* s1vln */){
      return new F(function(){return A1(_13f/* s1vll */,new T(function(){
        return  -E(_13h/* s1vln */);
      }));});
    },
    _13i/* s1vlu */ = new T(function(){
      return B(_128/* Text.Read.Lex.expect2 */(function(_13j/* s1vlt */){
        return new F(function(){return A3(_13b/* s1vli */,_13j/* s1vlt */, _13e/* s1vlk */, _13g/* s1vlm */);});
      }));
    }),
    _13k/* s1vlv */ = function(_13l/* s1vlw */){
      return E(_13i/* s1vlu */);
    },
    _13m/* s1vlx */ = function(_13n/* s1vly */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_13n/* s1vly */, _13k/* s1vlv */);});
    },
    _13o/* s1vlN */ = new T(function(){
      return B(_128/* Text.Read.Lex.expect2 */(function(_13p/* s1vlB */){
        var _13q/* s1vlC */ = E(_13p/* s1vlB */);
        if(_13q/* s1vlC */._==4){
          var _13r/* s1vlE */ = E(_13q/* s1vlC */.a);
          if(!_13r/* s1vlE */._){
            return new F(function(){return A3(_13b/* s1vli */,_13q/* s1vlC */, _13e/* s1vlk */, _13f/* s1vll */);});
          }else{
            if(E(_13r/* s1vlE */.a)==45){
              if(!E(_13r/* s1vlE */.b)._){
                return E(new T1(1,_13m/* s1vlx */));
              }else{
                return new F(function(){return A3(_13b/* s1vli */,_13q/* s1vlC */, _13e/* s1vlk */, _13f/* s1vll */);});
              }
            }else{
              return new F(function(){return A3(_13b/* s1vli */,_13q/* s1vlC */, _13e/* s1vlk */, _13f/* s1vll */);});
            }
          }
        }else{
          return new F(function(){return A3(_13b/* s1vli */,_13q/* s1vlC */, _13e/* s1vlk */, _13f/* s1vll */);});
        }
      }));
    }),
    _13s/* s1vlO */ = function(_13t/* s1vlP */){
      return E(_13o/* s1vlN */);
    };
    return new T1(1,function(_13u/* s1vlQ */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_13u/* s1vlQ */, _13s/* s1vlO */);});
    });
  };
  return new F(function(){return _12Z/* GHC.Read.$fReadDouble10 */(_13d/* s1vlS */, _13c/* s1vlj */);});
},
_13v/* $fReadDouble7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NaN"));
}),
_13w/* $fReadDouble8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Infinity"));
}),
_13x/* $fReadFloat4 */ = new T(function(){
  return 1/0;
}),
_13y/* $fReadFloat3 */ = function(_13z/* s1vhY */, _13A/* s1vhZ */){
  return new F(function(){return A1(_13A/* s1vhZ */,_13x/* GHC.Read.$fReadFloat4 */);});
},
_13B/* $fReadFloat6 */ = new T(function(){
  return 0/0;
}),
_13C/* $fReadFloat5 */ = function(_13D/* s1vhV */, _13E/* s1vhW */){
  return new F(function(){return A1(_13E/* s1vhW */,_13B/* GHC.Read.$fReadFloat6 */);});
},
_13F/* $fRealFloatDouble2 */ = 1024,
_13G/* $fRealFloatDouble3 */ = -1021,
_13H/* $fExceptionArithException_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_13I/* $fExceptionArithException_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GHC.Exception"));
}),
_13J/* $fExceptionArithException_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ArithException"));
}),
_13K/* $fExceptionArithException_wild */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_13H/* GHC.Exception.$fExceptionArithException_ww2 */,_13I/* GHC.Exception.$fExceptionArithException_ww4 */,_13J/* GHC.Exception.$fExceptionArithException_ww5 */),
_13L/* $fExceptionArithException8 */ = new T5(0,new Long/* EXTERNAL */(4194982440, 719304104, true),new Long/* EXTERNAL */(3110813675, 1843557400, true),_13K/* GHC.Exception.$fExceptionArithException_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_13M/* $fExceptionArithException7 */ = function(_13N/* s2SAg */){
  return E(_13L/* GHC.Exception.$fExceptionArithException8 */);
},
_13O/* $fExceptionArithException_$cfromException */ = function(_13P/* s2SAM */){
  var _13Q/* s2SAN */ = E(_13P/* s2SAM */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_13Q/* s2SAN */.a)), _13M/* GHC.Exception.$fExceptionArithException7 */, _13Q/* s2SAN */.b);});
},
_13R/* $fExceptionArithException1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ratio has zero denominator"));
}),
_13S/* $fExceptionArithException2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("denormal"));
}),
_13T/* $fExceptionArithException3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("divide by zero"));
}),
_13U/* $fExceptionArithException4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("loss of precision"));
}),
_13V/* $fExceptionArithException5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic underflow"));
}),
_13W/* $fExceptionArithException6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arithmetic overflow"));
}),
_13X/* $w$cshowsPrec */ = function(_13Y/* s2SAR */, _13Z/* s2SAS */){
  switch(E(_13Y/* s2SAR */)){
    case 0:
      return new F(function(){return _12/* GHC.Base.++ */(_13W/* GHC.Exception.$fExceptionArithException6 */, _13Z/* s2SAS */);});
      break;
    case 1:
      return new F(function(){return _12/* GHC.Base.++ */(_13V/* GHC.Exception.$fExceptionArithException5 */, _13Z/* s2SAS */);});
      break;
    case 2:
      return new F(function(){return _12/* GHC.Base.++ */(_13U/* GHC.Exception.$fExceptionArithException4 */, _13Z/* s2SAS */);});
      break;
    case 3:
      return new F(function(){return _12/* GHC.Base.++ */(_13T/* GHC.Exception.$fExceptionArithException3 */, _13Z/* s2SAS */);});
      break;
    case 4:
      return new F(function(){return _12/* GHC.Base.++ */(_13S/* GHC.Exception.$fExceptionArithException2 */, _13Z/* s2SAS */);});
      break;
    default:
      return new F(function(){return _12/* GHC.Base.++ */(_13R/* GHC.Exception.$fExceptionArithException1 */, _13Z/* s2SAS */);});
  }
},
_140/* $fExceptionArithException_$cshow */ = function(_141/* s2SAX */){
  return new F(function(){return _13X/* GHC.Exception.$w$cshowsPrec */(_141/* s2SAX */, _I/* GHC.Types.[] */);});
},
_142/* $fExceptionArithException_$cshowsPrec */ = function(_143/* s2SAU */, _144/* s2SAV */, _145/* s2SAW */){
  return new F(function(){return _13X/* GHC.Exception.$w$cshowsPrec */(_144/* s2SAV */, _145/* s2SAW */);});
},
_146/* $fShowArithException_$cshowList */ = function(_147/* s2SAY */, _148/* s2SAZ */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_13X/* GHC.Exception.$w$cshowsPrec */, _147/* s2SAY */, _148/* s2SAZ */);});
},
_149/* $fShowArithException */ = new T3(0,_142/* GHC.Exception.$fExceptionArithException_$cshowsPrec */,_140/* GHC.Exception.$fExceptionArithException_$cshow */,_146/* GHC.Exception.$fShowArithException_$cshowList */),
_14a/* $fExceptionArithException */ = new T(function(){
  return new T5(0,_13M/* GHC.Exception.$fExceptionArithException7 */,_149/* GHC.Exception.$fShowArithException */,_14b/* GHC.Exception.$fExceptionArithException_$ctoException */,_13O/* GHC.Exception.$fExceptionArithException_$cfromException */,_140/* GHC.Exception.$fExceptionArithException_$cshow */);
}),
_14b/* $fExceptionArithException_$ctoException */ = function(_Qi/* B1 */){
  return new T2(0,_14a/* GHC.Exception.$fExceptionArithException */,_Qi/* B1 */);
},
_14c/* DivideByZero */ = 3,
_14d/* divZeroException */ = new T(function(){
  return B(_14b/* GHC.Exception.$fExceptionArithException_$ctoException */(_14c/* GHC.Exception.DivideByZero */));
}),
_14e/* divZeroError */ = new T(function(){
  return die/* EXTERNAL */(_14d/* GHC.Exception.divZeroException */);
}),
_14f/* eqInteger */ = function(_14g/* s1H2 */, _14h/* s1H3 */){
  var _14i/* s1H4 */ = E(_14g/* s1H2 */);
  if(!_14i/* s1H4 */._){
    var _14j/* s1H5 */ = _14i/* s1H4 */.a,
    _14k/* s1H6 */ = E(_14h/* s1H3 */);
    return (_14k/* s1H6 */._==0) ? _14j/* s1H5 */==_14k/* s1H6 */.a : (I_compareInt/* EXTERNAL */(_14k/* s1H6 */.a, _14j/* s1H5 */)==0) ? true : false;
  }else{
    var _14l/* s1Hc */ = _14i/* s1H4 */.a,
    _14m/* s1Hd */ = E(_14h/* s1H3 */);
    return (_14m/* s1Hd */._==0) ? (I_compareInt/* EXTERNAL */(_14l/* s1Hc */, _14m/* s1Hd */.a)==0) ? true : false : (I_compare/* EXTERNAL */(_14l/* s1Hc */, _14m/* s1Hd */.a)==0) ? true : false;
  }
},
_14n/* even1 */ = new T1(0,0),
_14o/* remInteger */ = function(_14p/* s1NY */, _14q/* s1NZ */){
  while(1){
    var _14r/* s1O0 */ = E(_14p/* s1NY */);
    if(!_14r/* s1O0 */._){
      var _14s/* s1O2 */ = E(_14r/* s1O0 */.a);
      if(_14s/* s1O2 */==(-2147483648)){
        _14p/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _14t/* s1O3 */ = E(_14q/* s1NZ */);
        if(!_14t/* s1O3 */._){
          return new T1(0,_14s/* s1O2 */%_14t/* s1O3 */.a);
        }else{
          _14p/* s1NY */ = new T1(1,I_fromInt/* EXTERNAL */(_14s/* s1O2 */));
          _14q/* s1NZ */ = _14t/* s1O3 */;
          continue;
        }
      }
    }else{
      var _14u/* s1Od */ = _14r/* s1O0 */.a,
      _14v/* s1Oe */ = E(_14q/* s1NZ */);
      return (_14v/* s1Oe */._==0) ? new T1(1,I_rem/* EXTERNAL */(_14u/* s1Od */, I_fromInt/* EXTERNAL */(_14v/* s1Oe */.a))) : new T1(1,I_rem/* EXTERNAL */(_14u/* s1Od */, _14v/* s1Oe */.a));
    }
  }
},
_14w/* $fIntegralInteger_$crem */ = function(_14x/* svuo */, _14y/* svup */){
  if(!B(_14f/* GHC.Integer.Type.eqInteger */(_14y/* svup */, _14n/* GHC.Real.even1 */))){
    return new F(function(){return _14o/* GHC.Integer.Type.remInteger */(_14x/* svuo */, _14y/* svup */);});
  }else{
    return E(_14e/* GHC.Real.divZeroError */);
  }
},
_14z/* $fEnumRatio_gcd' */ = function(_14A/* svur */, _14B/* svus */){
  while(1){
    if(!B(_14f/* GHC.Integer.Type.eqInteger */(_14B/* svus */, _14n/* GHC.Real.even1 */))){
      var _14C/*  svur */ = _14B/* svus */,
      _14D/*  svus */ = B(_14w/* GHC.Real.$fIntegralInteger_$crem */(_14A/* svur */, _14B/* svus */));
      _14A/* svur */ = _14C/*  svur */;
      _14B/* svus */ = _14D/*  svus */;
      continue;
    }else{
      return E(_14A/* svur */);
    }
  }
},
_14E/* absInteger */ = function(_14F/* s1QP */){
  var _14G/* s1QQ */ = E(_14F/* s1QP */);
  if(!_14G/* s1QQ */._){
    var _14H/* s1QS */ = E(_14G/* s1QQ */.a);
    return (_14H/* s1QS */==(-2147483648)) ? E(_TQ/* GHC.Integer.Type.lvl3 */) : (_14H/* s1QS */<0) ? new T1(0, -_14H/* s1QS */) : E(_14G/* s1QQ */);
  }else{
    var _14I/* s1QW */ = _14G/* s1QQ */.a;
    return (I_compareInt/* EXTERNAL */(_14I/* s1QW */, 0)>=0) ? E(_14G/* s1QQ */) : new T1(1,I_negate/* EXTERNAL */(_14I/* s1QW */));
  }
},
_14J/* quotInteger */ = function(_14K/* s1On */, _14L/* s1Oo */){
  while(1){
    var _14M/* s1Op */ = E(_14K/* s1On */);
    if(!_14M/* s1Op */._){
      var _14N/* s1Or */ = E(_14M/* s1Op */.a);
      if(_14N/* s1Or */==(-2147483648)){
        _14K/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _14O/* s1Os */ = E(_14L/* s1Oo */);
        if(!_14O/* s1Os */._){
          return new T1(0,quot/* EXTERNAL */(_14N/* s1Or */, _14O/* s1Os */.a));
        }else{
          _14K/* s1On */ = new T1(1,I_fromInt/* EXTERNAL */(_14N/* s1Or */));
          _14L/* s1Oo */ = _14O/* s1Os */;
          continue;
        }
      }
    }else{
      var _14P/* s1OC */ = _14M/* s1Op */.a,
      _14Q/* s1OD */ = E(_14L/* s1Oo */);
      return (_14Q/* s1OD */._==0) ? new T1(0,I_toInt/* EXTERNAL */(I_quot/* EXTERNAL */(_14P/* s1OC */, I_fromInt/* EXTERNAL */(_14Q/* s1OD */.a)))) : new T1(1,I_quot/* EXTERNAL */(_14P/* s1OC */, _14Q/* s1OD */.a));
    }
  }
},
_14R/* RatioZeroDenominator */ = 5,
_14S/* ratioZeroDenomException */ = new T(function(){
  return B(_14b/* GHC.Exception.$fExceptionArithException_$ctoException */(_14R/* GHC.Exception.RatioZeroDenominator */));
}),
_14T/* ratioZeroDenominatorError */ = new T(function(){
  return die/* EXTERNAL */(_14S/* GHC.Exception.ratioZeroDenomException */);
}),
_14U/* $w$sreduce */ = function(_14V/* svvz */, _14W/* svvA */){
  if(!B(_14f/* GHC.Integer.Type.eqInteger */(_14W/* svvA */, _14n/* GHC.Real.even1 */))){
    var _14X/* svvC */ = B(_14z/* GHC.Real.$fEnumRatio_gcd' */(B(_14E/* GHC.Integer.Type.absInteger */(_14V/* svvz */)), B(_14E/* GHC.Integer.Type.absInteger */(_14W/* svvA */))));
    return (!B(_14f/* GHC.Integer.Type.eqInteger */(_14X/* svvC */, _14n/* GHC.Real.even1 */))) ? new T2(0,B(_14J/* GHC.Integer.Type.quotInteger */(_14V/* svvz */, _14X/* svvC */)),B(_14J/* GHC.Integer.Type.quotInteger */(_14W/* svvA */, _14X/* svvC */))) : E(_14e/* GHC.Real.divZeroError */);
  }else{
    return E(_14T/* GHC.Real.ratioZeroDenominatorError */);
  }
},
_14Y/* $fEnumRatio1 */ = new T1(0,1),
_14Z/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Negative exponent"));
}),
_150/* ^1 */ = new T(function(){
  return B(err/* EXTERNAL */(_14Z/* GHC.Real.lvl */));
}),
_151/* even2 */ = new T1(0,2),
_152/* even3 */ = new T(function(){
  return B(_14f/* GHC.Integer.Type.eqInteger */(_151/* GHC.Real.even2 */, _14n/* GHC.Real.even1 */));
}),
_153/* minusInteger */ = function(_154/* s1P0 */, _155/* s1P1 */){
  while(1){
    var _156/* s1P2 */ = E(_154/* s1P0 */);
    if(!_156/* s1P2 */._){
      var _157/* s1P3 */ = _156/* s1P2 */.a,
      _158/* s1P4 */ = E(_155/* s1P1 */);
      if(!_158/* s1P4 */._){
        var _159/* s1P5 */ = _158/* s1P4 */.a,
        _15a/* s1P6 */ = subC/* EXTERNAL */(_157/* s1P3 */, _159/* s1P5 */);
        if(!E(_15a/* s1P6 */.b)){
          return new T1(0,_15a/* s1P6 */.a);
        }else{
          _154/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_157/* s1P3 */));
          _155/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_159/* s1P5 */));
          continue;
        }
      }else{
        _154/* s1P0 */ = new T1(1,I_fromInt/* EXTERNAL */(_157/* s1P3 */));
        _155/* s1P1 */ = _158/* s1P4 */;
        continue;
      }
    }else{
      var _15b/* s1Pl */ = E(_155/* s1P1 */);
      if(!_15b/* s1Pl */._){
        _154/* s1P0 */ = _156/* s1P2 */;
        _155/* s1P1 */ = new T1(1,I_fromInt/* EXTERNAL */(_15b/* s1Pl */.a));
        continue;
      }else{
        return new T1(1,I_sub/* EXTERNAL */(_156/* s1P2 */.a, _15b/* s1Pl */.a));
      }
    }
  }
},
_15c/* g */ = function(_15d/* svof */, _15e/* svog */, _15f/* svoh */){
  while(1){
    if(!E(_152/* GHC.Real.even3 */)){
      if(!B(_14f/* GHC.Integer.Type.eqInteger */(B(_14o/* GHC.Integer.Type.remInteger */(_15e/* svog */, _151/* GHC.Real.even2 */)), _14n/* GHC.Real.even1 */))){
        if(!B(_14f/* GHC.Integer.Type.eqInteger */(_15e/* svog */, _14Y/* GHC.Real.$fEnumRatio1 */))){
          var _15g/*  svof */ = B(_U7/* GHC.Integer.Type.timesInteger */(_15d/* svof */, _15d/* svof */)),
          _15h/*  svog */ = B(_14J/* GHC.Integer.Type.quotInteger */(B(_153/* GHC.Integer.Type.minusInteger */(_15e/* svog */, _14Y/* GHC.Real.$fEnumRatio1 */)), _151/* GHC.Real.even2 */)),
          _15i/*  svoh */ = B(_U7/* GHC.Integer.Type.timesInteger */(_15d/* svof */, _15f/* svoh */));
          _15d/* svof */ = _15g/*  svof */;
          _15e/* svog */ = _15h/*  svog */;
          _15f/* svoh */ = _15i/*  svoh */;
          continue;
        }else{
          return new F(function(){return _U7/* GHC.Integer.Type.timesInteger */(_15d/* svof */, _15f/* svoh */);});
        }
      }else{
        var _15g/*  svof */ = B(_U7/* GHC.Integer.Type.timesInteger */(_15d/* svof */, _15d/* svof */)),
        _15h/*  svog */ = B(_14J/* GHC.Integer.Type.quotInteger */(_15e/* svog */, _151/* GHC.Real.even2 */));
        _15d/* svof */ = _15g/*  svof */;
        _15e/* svog */ = _15h/*  svog */;
        continue;
      }
    }else{
      return E(_14e/* GHC.Real.divZeroError */);
    }
  }
},
_15j/* ^_f */ = function(_15k/* svot */, _15l/* svou */){
  while(1){
    if(!E(_152/* GHC.Real.even3 */)){
      if(!B(_14f/* GHC.Integer.Type.eqInteger */(B(_14o/* GHC.Integer.Type.remInteger */(_15l/* svou */, _151/* GHC.Real.even2 */)), _14n/* GHC.Real.even1 */))){
        if(!B(_14f/* GHC.Integer.Type.eqInteger */(_15l/* svou */, _14Y/* GHC.Real.$fEnumRatio1 */))){
          return new F(function(){return _15c/* GHC.Real.g */(B(_U7/* GHC.Integer.Type.timesInteger */(_15k/* svot */, _15k/* svot */)), B(_14J/* GHC.Integer.Type.quotInteger */(B(_153/* GHC.Integer.Type.minusInteger */(_15l/* svou */, _14Y/* GHC.Real.$fEnumRatio1 */)), _151/* GHC.Real.even2 */)), _15k/* svot */);});
        }else{
          return E(_15k/* svot */);
        }
      }else{
        var _15m/*  svot */ = B(_U7/* GHC.Integer.Type.timesInteger */(_15k/* svot */, _15k/* svot */)),
        _15n/*  svou */ = B(_14J/* GHC.Integer.Type.quotInteger */(_15l/* svou */, _151/* GHC.Real.even2 */));
        _15k/* svot */ = _15m/*  svot */;
        _15l/* svou */ = _15n/*  svou */;
        continue;
      }
    }else{
      return E(_14e/* GHC.Real.divZeroError */);
    }
  }
},
_15o/* ltInteger */ = function(_15p/* s1FJ */, _15q/* s1FK */){
  var _15r/* s1FL */ = E(_15p/* s1FJ */);
  if(!_15r/* s1FL */._){
    var _15s/* s1FM */ = _15r/* s1FL */.a,
    _15t/* s1FN */ = E(_15q/* s1FK */);
    return (_15t/* s1FN */._==0) ? _15s/* s1FM */<_15t/* s1FN */.a : I_compareInt/* EXTERNAL */(_15t/* s1FN */.a, _15s/* s1FM */)>0;
  }else{
    var _15u/* s1FU */ = _15r/* s1FL */.a,
    _15v/* s1FV */ = E(_15q/* s1FK */);
    return (_15v/* s1FV */._==0) ? I_compareInt/* EXTERNAL */(_15u/* s1FU */, _15v/* s1FV */.a)<0 : I_compare/* EXTERNAL */(_15u/* s1FU */, _15v/* s1FV */.a)<0;
  }
},
_15w/* ^_$s^ */ = function(_15x/* svoF */, _15y/* svoG */){
  if(!B(_15o/* GHC.Integer.Type.ltInteger */(_15y/* svoG */, _14n/* GHC.Real.even1 */))){
    if(!B(_14f/* GHC.Integer.Type.eqInteger */(_15y/* svoG */, _14n/* GHC.Real.even1 */))){
      return new F(function(){return _15j/* GHC.Real.^_f */(_15x/* svoF */, _15y/* svoG */);});
    }else{
      return E(_14Y/* GHC.Real.$fEnumRatio1 */);
    }
  }else{
    return E(_150/* GHC.Real.^1 */);
  }
},
_15z/* lvl38 */ = new T1(0,1),
_15A/* lvl */ = new T1(0,0),
_15B/* lvl1 */ = new T1(0,-1),
_15C/* signumInteger */ = function(_15D/* s1OO */){
  var _15E/* s1OP */ = E(_15D/* s1OO */);
  if(!_15E/* s1OP */._){
    var _15F/* s1OQ */ = _15E/* s1OP */.a;
    return (_15F/* s1OQ */>=0) ? (E(_15F/* s1OQ */)==0) ? E(_15A/* GHC.Integer.Type.lvl */) : E(_TF/* GHC.Integer.Type.log2I1 */) : E(_15B/* GHC.Integer.Type.lvl1 */);
  }else{
    var _15G/* s1OW */ = I_compareInt/* EXTERNAL */(_15E/* s1OP */.a, 0);
    return (_15G/* s1OW */<=0) ? (E(_15G/* s1OW */)==0) ? E(_15A/* GHC.Integer.Type.lvl */) : E(_15B/* GHC.Integer.Type.lvl1 */) : E(_TF/* GHC.Integer.Type.log2I1 */);
  }
},
_15H/* $wfracExp */ = function(_15I/* s1oeV */, _15J/* s1oeW */, _15K/* s1oeX */){
  while(1){
    var _15L/* s1oeY */ = E(_15K/* s1oeX */);
    if(!_15L/* s1oeY */._){
      if(!B(_15o/* GHC.Integer.Type.ltInteger */(_15I/* s1oeV */, _Uk/* Text.Read.Lex.numberToFixed3 */))){
        return new T2(0,B(_U7/* GHC.Integer.Type.timesInteger */(_15J/* s1oeW */, B(_15w/* GHC.Real.^_$s^ */(_TV/* Text.Read.Lex.numberToFixed1 */, _15I/* s1oeV */)))),_14Y/* GHC.Real.$fEnumRatio1 */);
      }else{
        var _15M/* s1of2 */ = B(_15w/* GHC.Real.^_$s^ */(_TV/* Text.Read.Lex.numberToFixed1 */, B(_TR/* GHC.Integer.Type.negateInteger */(_15I/* s1oeV */))));
        return new F(function(){return _14U/* GHC.Real.$w$sreduce */(B(_U7/* GHC.Integer.Type.timesInteger */(_15J/* s1oeW */, B(_15C/* GHC.Integer.Type.signumInteger */(_15M/* s1of2 */)))), B(_14E/* GHC.Integer.Type.absInteger */(_15M/* s1of2 */)));});
      }
    }else{
      var _15N/*  s1oeV */ = B(_153/* GHC.Integer.Type.minusInteger */(_15I/* s1oeV */, _15z/* Text.Read.Lex.lvl38 */)),
      _15O/*  s1oeW */ = B(_TH/* GHC.Integer.Type.plusInteger */(B(_U7/* GHC.Integer.Type.timesInteger */(_15J/* s1oeW */, _TV/* Text.Read.Lex.numberToFixed1 */)), B(_U1/* GHC.Integer.Type.smallInteger */(E(_15L/* s1oeY */.a)))));
      _15I/* s1oeV */ = _15N/*  s1oeV */;
      _15J/* s1oeW */ = _15O/*  s1oeW */;
      _15K/* s1oeX */ = _15L/* s1oeY */.b;
      continue;
    }
  }
},
_15P/* geInteger */ = function(_15Q/* s1Fo */, _15R/* s1Fp */){
  var _15S/* s1Fq */ = E(_15Q/* s1Fo */);
  if(!_15S/* s1Fq */._){
    var _15T/* s1Fr */ = _15S/* s1Fq */.a,
    _15U/* s1Fs */ = E(_15R/* s1Fp */);
    return (_15U/* s1Fs */._==0) ? _15T/* s1Fr */>=_15U/* s1Fs */.a : I_compareInt/* EXTERNAL */(_15U/* s1Fs */.a, _15T/* s1Fr */)<=0;
  }else{
    var _15V/* s1Fz */ = _15S/* s1Fq */.a,
    _15W/* s1FA */ = E(_15R/* s1Fp */);
    return (_15W/* s1FA */._==0) ? I_compareInt/* EXTERNAL */(_15V/* s1Fz */, _15W/* s1FA */.a)>=0 : I_compare/* EXTERNAL */(_15V/* s1Fz */, _15W/* s1FA */.a)>=0;
  }
},
_15X/* $wnumberToRational */ = function(_15Y/* s1oil */){
  var _15Z/* s1oim */ = E(_15Y/* s1oil */);
  if(!_15Z/* s1oim */._){
    var _160/* s1oio */ = _15Z/* s1oim */.b;
    return new F(function(){return _14U/* GHC.Real.$w$sreduce */(B(_U7/* GHC.Integer.Type.timesInteger */(B(_Ul/* Text.Read.Lex.numberToFixed_go */(new T(function(){
      return B(_U1/* GHC.Integer.Type.smallInteger */(E(_15Z/* s1oim */.a)));
    }), new T(function(){
      return B(_TW/* GHC.List.$wlenAcc */(_160/* s1oio */, 0));
    },1), B(_2S/* GHC.Base.map */(_U3/* Text.Read.Lex.numberToFixed2 */, _160/* s1oio */)))), _15z/* Text.Read.Lex.lvl38 */)), _15z/* Text.Read.Lex.lvl38 */);});
  }else{
    var _161/* s1oix */ = _15Z/* s1oim */.a,
    _162/* s1oiz */ = _15Z/* s1oim */.c,
    _163/* s1oiA */ = E(_15Z/* s1oim */.b);
    if(!_163/* s1oiA */._){
      var _164/* s1oiB */ = E(_162/* s1oiz */);
      if(!_164/* s1oiB */._){
        return new F(function(){return _14U/* GHC.Real.$w$sreduce */(B(_U7/* GHC.Integer.Type.timesInteger */(B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _161/* s1oix */)), _15z/* Text.Read.Lex.lvl38 */)), _15z/* Text.Read.Lex.lvl38 */);});
      }else{
        var _165/* s1oiE */ = _164/* s1oiB */.a;
        if(!B(_15P/* GHC.Integer.Type.geInteger */(_165/* s1oiE */, _Uk/* Text.Read.Lex.numberToFixed3 */))){
          var _166/* s1oiG */ = B(_15w/* GHC.Real.^_$s^ */(_TV/* Text.Read.Lex.numberToFixed1 */, B(_TR/* GHC.Integer.Type.negateInteger */(_165/* s1oiE */))));
          return new F(function(){return _14U/* GHC.Real.$w$sreduce */(B(_U7/* GHC.Integer.Type.timesInteger */(B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _161/* s1oix */)), B(_15C/* GHC.Integer.Type.signumInteger */(_166/* s1oiG */)))), B(_14E/* GHC.Integer.Type.absInteger */(_166/* s1oiG */)));});
        }else{
          return new F(function(){return _14U/* GHC.Real.$w$sreduce */(B(_U7/* GHC.Integer.Type.timesInteger */(B(_U7/* GHC.Integer.Type.timesInteger */(B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _161/* s1oix */)), B(_15w/* GHC.Real.^_$s^ */(_TV/* Text.Read.Lex.numberToFixed1 */, _165/* s1oiE */)))), _15z/* Text.Read.Lex.lvl38 */)), _15z/* Text.Read.Lex.lvl38 */);});
        }
      }
    }else{
      var _167/* s1oiQ */ = _163/* s1oiA */.a,
      _168/* s1oiR */ = E(_162/* s1oiz */);
      if(!_168/* s1oiR */._){
        return new F(function(){return _15H/* Text.Read.Lex.$wfracExp */(_Uk/* Text.Read.Lex.numberToFixed3 */, B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _161/* s1oix */)), _167/* s1oiQ */);});
      }else{
        return new F(function(){return _15H/* Text.Read.Lex.$wfracExp */(_168/* s1oiR */.a, B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _161/* s1oix */)), _167/* s1oiQ */);});
      }
    }
  }
},
_169/* dropWhile */ = function(_16a/* s9xE */, _16b/* s9xF */){
  while(1){
    var _16c/* s9xG */ = E(_16b/* s9xF */);
    if(!_16c/* s9xG */._){
      return __Z/* EXTERNAL */;
    }else{
      if(!B(A1(_16a/* s9xE */,_16c/* s9xG */.a))){
        return E(_16c/* s9xG */);
      }else{
        _16b/* s9xF */ = _16c/* s9xG */.b;
        continue;
      }
    }
  }
},
_16d/* gtInteger */ = function(_16e/* s1G4 */, _16f/* s1G5 */){
  var _16g/* s1G6 */ = E(_16e/* s1G4 */);
  if(!_16g/* s1G6 */._){
    var _16h/* s1G7 */ = _16g/* s1G6 */.a,
    _16i/* s1G8 */ = E(_16f/* s1G5 */);
    return (_16i/* s1G8 */._==0) ? _16h/* s1G7 */>_16i/* s1G8 */.a : I_compareInt/* EXTERNAL */(_16i/* s1G8 */.a, _16h/* s1G7 */)<0;
  }else{
    var _16j/* s1Gf */ = _16g/* s1G6 */.a,
    _16k/* s1Gg */ = E(_16f/* s1G5 */);
    return (_16k/* s1Gg */._==0) ? I_compareInt/* EXTERNAL */(_16j/* s1Gf */, _16k/* s1Gg */.a)>0 : I_compare/* EXTERNAL */(_16j/* s1Gf */, _16k/* s1Gg */.a)>0;
  }
},
_16l/* $fShowLexeme2 */ = 0,
_16m/* eqInt */ = function(_16n/* scFg */, _16o/* scFh */){
  return E(_16n/* scFg */)==E(_16o/* scFh */);
},
_16p/* numberToRangedRational1 */ = function(_16q/* B1 */){
  return new F(function(){return _16m/* GHC.Classes.eqInt */(_16l/* Text.Read.Lex.$fShowLexeme2 */, _16q/* B1 */);});
},
_16r/* numberToRangedRational3 */ = new T2(0,E(_Uk/* Text.Read.Lex.numberToFixed3 */),E(_14Y/* GHC.Real.$fEnumRatio1 */)),
_16s/* numberToRangedRational2 */ = new T1(1,_16r/* Text.Read.Lex.numberToRangedRational3 */),
_16t/* numberToRangedRational4 */ = new T1(0,-2147483648),
_16u/* numberToRangedRational5 */ = new T1(0,2147483647),
_16v/* $wnumberToRangedRational */ = function(_16w/* s1ovV */, _16x/* s1ovW */, _16y/* s1ovX */){
  var _16z/* s1ovY */ = E(_16y/* s1ovX */);
  if(!_16z/* s1ovY */._){
    return new T1(1,new T(function(){
      var _16A/* s1ow1 */ = B(_15X/* Text.Read.Lex.$wnumberToRational */(_16z/* s1ovY */));
      return new T2(0,E(_16A/* s1ow1 */.a),E(_16A/* s1ow1 */.b));
    }));
  }else{
    var _16B/* s1ow8 */ = E(_16z/* s1ovY */.c);
    if(!_16B/* s1ow8 */._){
      return new T1(1,new T(function(){
        var _16C/* s1ow9 */ = B(_15X/* Text.Read.Lex.$wnumberToRational */(_16z/* s1ovY */));
        return new T2(0,E(_16C/* s1ow9 */.a),E(_16C/* s1ow9 */.b));
      }));
    }else{
      var _16D/* s1owd */ = _16B/* s1ow8 */.a;
      if(!B(_16d/* GHC.Integer.Type.gtInteger */(_16D/* s1owd */, _16u/* Text.Read.Lex.numberToRangedRational5 */))){
        if(!B(_15o/* GHC.Integer.Type.ltInteger */(_16D/* s1owd */, _16t/* Text.Read.Lex.numberToRangedRational4 */))){
          var _16E/* s1owg */ = function(_16F/* s1owh */){
            var _16G/* s1owl */ = _16F/* s1owh */+B(_Vw/* GHC.Integer.Type.integerToInt */(_16D/* s1owd */))|0;
            return (_16G/* s1owl */<=(E(_16x/* s1ovW */)+3|0)) ? (_16G/* s1owl */>=(E(_16w/* s1ovV */)-3|0)) ? new T1(1,new T(function(){
              var _16H/* s1owu */ = B(_15X/* Text.Read.Lex.$wnumberToRational */(_16z/* s1ovY */));
              return new T2(0,E(_16H/* s1owu */.a),E(_16H/* s1owu */.b));
            })) : E(_16s/* Text.Read.Lex.numberToRangedRational2 */) : __Z/* EXTERNAL */;
          },
          _16I/* s1owy */ = B(_169/* GHC.List.dropWhile */(_16p/* Text.Read.Lex.numberToRangedRational1 */, _16z/* s1ovY */.a));
          if(!_16I/* s1owy */._){
            var _16J/* s1owz */ = E(_16z/* s1ovY */.b);
            if(!_16J/* s1owz */._){
              return E(_16s/* Text.Read.Lex.numberToRangedRational2 */);
            }else{
              var _16K/* s1owB */ = B(_Qj/* GHC.List.$wspan */(_16p/* Text.Read.Lex.numberToRangedRational1 */, _16J/* s1owz */.a));
              if(!E(_16K/* s1owB */.b)._){
                return E(_16s/* Text.Read.Lex.numberToRangedRational2 */);
              }else{
                return new F(function(){return _16E/* s1owg */( -B(_TW/* GHC.List.$wlenAcc */(_16K/* s1owB */.a, 0)));});
              }
            }
          }else{
            return new F(function(){return _16E/* s1owg */(B(_TW/* GHC.List.$wlenAcc */(_16I/* s1owy */, 0)));});
          }
        }else{
          return __Z/* EXTERNAL */;
        }
      }else{
        return __Z/* EXTERNAL */;
      }
    }
  }
},
_16L/* pfail1 */ = function(_16M/* s1kH8 */, _16N/* s1kH9 */){
  return new T0(2);
},
_16O/* $fRealDouble1 */ = new T1(0,1),
_16P/* compareInteger */ = function(_16Q/* s1Hk */, _16R/* s1Hl */){
  var _16S/* s1Hm */ = E(_16Q/* s1Hk */);
  if(!_16S/* s1Hm */._){
    var _16T/* s1Hn */ = _16S/* s1Hm */.a,
    _16U/* s1Ho */ = E(_16R/* s1Hl */);
    if(!_16U/* s1Ho */._){
      var _16V/* s1Hp */ = _16U/* s1Ho */.a;
      return (_16T/* s1Hn */!=_16V/* s1Hp */) ? (_16T/* s1Hn */>_16V/* s1Hp */) ? 2 : 0 : 1;
    }else{
      var _16W/* s1Hw */ = I_compareInt/* EXTERNAL */(_16U/* s1Ho */.a, _16T/* s1Hn */);
      return (_16W/* s1Hw */<=0) ? (_16W/* s1Hw */>=0) ? 1 : 2 : 0;
    }
  }else{
    var _16X/* s1HB */ = _16S/* s1Hm */.a,
    _16Y/* s1HC */ = E(_16R/* s1Hl */);
    if(!_16Y/* s1HC */._){
      var _16Z/* s1HF */ = I_compareInt/* EXTERNAL */(_16X/* s1HB */, _16Y/* s1HC */.a);
      return (_16Z/* s1HF */>=0) ? (_16Z/* s1HF */<=0) ? 1 : 2 : 0;
    }else{
      var _170/* s1HM */ = I_compare/* EXTERNAL */(_16X/* s1HB */, _16Y/* s1HC */.a);
      return (_170/* s1HM */>=0) ? (_170/* s1HM */<=0) ? 1 : 2 : 0;
    }
  }
},
_171/* encodeFloatInteger */ = function(_172/* s1LO */, _173/* s1LP */){
  var _174/* s1LQ */ = E(_172/* s1LO */);
  return (_174/* s1LQ */._==0) ? _174/* s1LQ */.a*Math.pow/* EXTERNAL */(2, _173/* s1LP */) : I_toNumber/* EXTERNAL */(_174/* s1LQ */.a)*Math.pow/* EXTERNAL */(2, _173/* s1LP */);
},
_175/* quotRemInteger */ = function(_176/* s1Ma */, _177/* s1Mb */){
  while(1){
    var _178/* s1Mc */ = E(_176/* s1Ma */);
    if(!_178/* s1Mc */._){
      var _179/* s1Me */ = E(_178/* s1Mc */.a);
      if(_179/* s1Me */==(-2147483648)){
        _176/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(-2147483648));
        continue;
      }else{
        var _17a/* s1Mf */ = E(_177/* s1Mb */);
        if(!_17a/* s1Mf */._){
          var _17b/* s1Mg */ = _17a/* s1Mf */.a;
          return new T2(0,new T1(0,quot/* EXTERNAL */(_179/* s1Me */, _17b/* s1Mg */)),new T1(0,_179/* s1Me */%_17b/* s1Mg */));
        }else{
          _176/* s1Ma */ = new T1(1,I_fromInt/* EXTERNAL */(_179/* s1Me */));
          _177/* s1Mb */ = _17a/* s1Mf */;
          continue;
        }
      }
    }else{
      var _17c/* s1Mt */ = E(_177/* s1Mb */);
      if(!_17c/* s1Mt */._){
        _176/* s1Ma */ = _178/* s1Mc */;
        _177/* s1Mb */ = new T1(1,I_fromInt/* EXTERNAL */(_17c/* s1Mt */.a));
        continue;
      }else{
        var _17d/* s1MA */ = I_quotRem/* EXTERNAL */(_178/* s1Mc */.a, _17c/* s1Mt */.a);
        return new T2(0,new T1(1,_17d/* s1MA */.a),new T1(1,_17d/* s1MA */.b));
      }
    }
  }
},
_17e/* rationalToDouble5 */ = new T1(0,0),
_17f/* shiftLInteger */ = function(_17g/* s1Jk */, _17h/* s1Jl */){
  while(1){
    var _17i/* s1Jm */ = E(_17g/* s1Jk */);
    if(!_17i/* s1Jm */._){
      _17g/* s1Jk */ = new T1(1,I_fromInt/* EXTERNAL */(_17i/* s1Jm */.a));
      continue;
    }else{
      return new T1(1,I_shiftLeft/* EXTERNAL */(_17i/* s1Jm */.a, _17h/* s1Jl */));
    }
  }
},
_17j/* $w$j */ = function(_17k/* s18Qg */, _17l/* s18Qh */, _17m/* s18Qi */){
  if(!B(_14f/* GHC.Integer.Type.eqInteger */(_17m/* s18Qi */, _17e/* GHC.Float.rationalToDouble5 */))){
    var _17n/* s18Qk */ = B(_175/* GHC.Integer.Type.quotRemInteger */(_17l/* s18Qh */, _17m/* s18Qi */)),
    _17o/* s18Ql */ = _17n/* s18Qk */.a;
    switch(B(_16P/* GHC.Integer.Type.compareInteger */(B(_17f/* GHC.Integer.Type.shiftLInteger */(_17n/* s18Qk */.b, 1)), _17m/* s18Qi */))){
      case 0:
        return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_17o/* s18Ql */, _17k/* s18Qg */);});
        break;
      case 1:
        if(!(B(_Vw/* GHC.Integer.Type.integerToInt */(_17o/* s18Ql */))&1)){
          return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_17o/* s18Ql */, _17k/* s18Qg */);});
        }else{
          return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_17o/* s18Ql */, _16O/* GHC.Float.$fRealDouble1 */)), _17k/* s18Qg */);});
        }
        break;
      default:
        return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_17o/* s18Ql */, _16O/* GHC.Float.$fRealDouble1 */)), _17k/* s18Qg */);});
    }
  }else{
    return E(_14e/* GHC.Real.divZeroError */);
  }
},
_17p/* log2I */ = function(_17q/* s1Ju */){
  var _17r/* s1Jv */ = function(_17s/* s1Jw */, _17t/* s1Jx */){
    while(1){
      if(!B(_15o/* GHC.Integer.Type.ltInteger */(_17s/* s1Jw */, _17q/* s1Ju */))){
        if(!B(_16d/* GHC.Integer.Type.gtInteger */(_17s/* s1Jw */, _17q/* s1Ju */))){
          if(!B(_14f/* GHC.Integer.Type.eqInteger */(_17s/* s1Jw */, _17q/* s1Ju */))){
            return new F(function(){return _QF/* Control.Exception.Base.patError */("GHC/Integer/Type.lhs:(553,5)-(555,32)|function l2");});
          }else{
            return E(_17t/* s1Jx */);
          }
        }else{
          return _17t/* s1Jx */-1|0;
        }
      }else{
        var _17u/*  s1Jw */ = B(_17f/* GHC.Integer.Type.shiftLInteger */(_17s/* s1Jw */, 1)),
        _17v/*  s1Jx */ = _17t/* s1Jx */+1|0;
        _17s/* s1Jw */ = _17u/*  s1Jw */;
        _17t/* s1Jx */ = _17v/*  s1Jx */;
        continue;
      }
    }
  };
  return new F(function(){return _17r/* s1Jv */(_TF/* GHC.Integer.Type.log2I1 */, 0);});
},
_17w/* integerLog2# */ = function(_17x/* s1JD */){
  var _17y/* s1JE */ = E(_17x/* s1JD */);
  if(!_17y/* s1JE */._){
    var _17z/* s1JG */ = _17y/* s1JE */.a>>>0;
    if(!_17z/* s1JG */){
      return -1;
    }else{
      var _17A/* s1JH */ = function(_17B/* s1JI */, _17C/* s1JJ */){
        while(1){
          if(_17B/* s1JI */>=_17z/* s1JG */){
            if(_17B/* s1JI */<=_17z/* s1JG */){
              if(_17B/* s1JI */!=_17z/* s1JG */){
                return new F(function(){return _QF/* Control.Exception.Base.patError */("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_17C/* s1JJ */);
              }
            }else{
              return _17C/* s1JJ */-1|0;
            }
          }else{
            var _17D/*  s1JI */ = imul/* EXTERNAL */(_17B/* s1JI */, 2)>>>0,
            _17E/*  s1JJ */ = _17C/* s1JJ */+1|0;
            _17B/* s1JI */ = _17D/*  s1JI */;
            _17C/* s1JJ */ = _17E/*  s1JJ */;
            continue;
          }
        }
      };
      return new F(function(){return _17A/* s1JH */(1, 0);});
    }
  }else{
    return new F(function(){return _17p/* GHC.Integer.Type.log2I */(_17y/* s1JE */);});
  }
},
_17F/* integerLog2IsPowerOf2# */ = function(_17G/* s1JT */){
  var _17H/* s1JU */ = E(_17G/* s1JT */);
  if(!_17H/* s1JU */._){
    var _17I/* s1JW */ = _17H/* s1JU */.a>>>0;
    if(!_17I/* s1JW */){
      return new T2(0,-1,0);
    }else{
      var _17J/* s1JX */ = function(_17K/* s1JY */, _17L/* s1JZ */){
        while(1){
          if(_17K/* s1JY */>=_17I/* s1JW */){
            if(_17K/* s1JY */<=_17I/* s1JW */){
              if(_17K/* s1JY */!=_17I/* s1JW */){
                return new F(function(){return _QF/* Control.Exception.Base.patError */("GHC/Integer/Type.lhs:(609,5)-(611,40)|function l2");});
              }else{
                return E(_17L/* s1JZ */);
              }
            }else{
              return _17L/* s1JZ */-1|0;
            }
          }else{
            var _17M/*  s1JY */ = imul/* EXTERNAL */(_17K/* s1JY */, 2)>>>0,
            _17N/*  s1JZ */ = _17L/* s1JZ */+1|0;
            _17K/* s1JY */ = _17M/*  s1JY */;
            _17L/* s1JZ */ = _17N/*  s1JZ */;
            continue;
          }
        }
      };
      return new T2(0,B(_17J/* s1JX */(1, 0)),(_17I/* s1JW */&_17I/* s1JW */-1>>>0)>>>0&4294967295);
    }
  }else{
    var _17O/* s1Kc */ = _17H/* s1JU */.a;
    return new T2(0,B(_17w/* GHC.Integer.Type.integerLog2# */(_17H/* s1JU */)),I_compareInt/* EXTERNAL */(I_and/* EXTERNAL */(_17O/* s1Kc */, I_sub/* EXTERNAL */(_17O/* s1Kc */, I_fromInt/* EXTERNAL */(1))), 0));
  }
},
_17P/* andInteger */ = function(_17Q/* s1Lf */, _17R/* s1Lg */){
  while(1){
    var _17S/* s1Lh */ = E(_17Q/* s1Lf */);
    if(!_17S/* s1Lh */._){
      var _17T/* s1Li */ = _17S/* s1Lh */.a,
      _17U/* s1Lj */ = E(_17R/* s1Lg */);
      if(!_17U/* s1Lj */._){
        return new T1(0,(_17T/* s1Li */>>>0&_17U/* s1Lj */.a>>>0)>>>0&4294967295);
      }else{
        _17Q/* s1Lf */ = new T1(1,I_fromInt/* EXTERNAL */(_17T/* s1Li */));
        _17R/* s1Lg */ = _17U/* s1Lj */;
        continue;
      }
    }else{
      var _17V/* s1Lu */ = E(_17R/* s1Lg */);
      if(!_17V/* s1Lu */._){
        _17Q/* s1Lf */ = _17S/* s1Lh */;
        _17R/* s1Lg */ = new T1(1,I_fromInt/* EXTERNAL */(_17V/* s1Lu */.a));
        continue;
      }else{
        return new T1(1,I_and/* EXTERNAL */(_17S/* s1Lh */.a, _17V/* s1Lu */.a));
      }
    }
  }
},
_17W/* roundingMode#1 */ = new T1(0,2),
_17X/* roundingMode# */ = function(_17Y/* s1Pt */, _17Z/* s1Pu */){
  var _180/* s1Pv */ = E(_17Y/* s1Pt */);
  if(!_180/* s1Pv */._){
    var _181/* s1Px */ = (_180/* s1Pv */.a>>>0&(2<<_17Z/* s1Pu */>>>0)-1>>>0)>>>0,
    _182/* s1PB */ = 1<<_17Z/* s1Pu */>>>0;
    return (_182/* s1PB */<=_181/* s1Px */) ? (_182/* s1PB */>=_181/* s1Px */) ? 1 : 2 : 0;
  }else{
    var _183/* s1PH */ = B(_17P/* GHC.Integer.Type.andInteger */(_180/* s1Pv */, B(_153/* GHC.Integer.Type.minusInteger */(B(_17f/* GHC.Integer.Type.shiftLInteger */(_17W/* GHC.Integer.Type.roundingMode#1 */, _17Z/* s1Pu */)), _TF/* GHC.Integer.Type.log2I1 */)))),
    _184/* s1PK */ = B(_17f/* GHC.Integer.Type.shiftLInteger */(_TF/* GHC.Integer.Type.log2I1 */, _17Z/* s1Pu */));
    return (!B(_16d/* GHC.Integer.Type.gtInteger */(_184/* s1PK */, _183/* s1PH */))) ? (!B(_15o/* GHC.Integer.Type.ltInteger */(_184/* s1PK */, _183/* s1PH */))) ? 1 : 2 : 0;
  }
},
_185/* shiftRInteger */ = function(_186/* s1Ja */, _187/* s1Jb */){
  while(1){
    var _188/* s1Jc */ = E(_186/* s1Ja */);
    if(!_188/* s1Jc */._){
      _186/* s1Ja */ = new T1(1,I_fromInt/* EXTERNAL */(_188/* s1Jc */.a));
      continue;
    }else{
      return new T1(1,I_shiftRight/* EXTERNAL */(_188/* s1Jc */.a, _187/* s1Jb */));
    }
  }
},
_189/* $w$sfromRat''1 */ = function(_18a/* s18Qu */, _18b/* s18Qv */, _18c/* s18Qw */, _18d/* s18Qx */){
  var _18e/* s18Qy */ = B(_17F/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_18d/* s18Qx */)),
  _18f/* s18Qz */ = _18e/* s18Qy */.a;
  if(!E(_18e/* s18Qy */.b)){
    var _18g/* s18QZ */ = B(_17w/* GHC.Integer.Type.integerLog2# */(_18c/* s18Qw */));
    if(_18g/* s18QZ */<((_18f/* s18Qz */+_18a/* s18Qu */|0)-1|0)){
      var _18h/* s18R4 */ = _18f/* s18Qz */+(_18a/* s18Qu */-_18b/* s18Qv */|0)|0;
      if(_18h/* s18R4 */>0){
        if(_18h/* s18R4 */>_18g/* s18QZ */){
          if(_18h/* s18R4 */<=(_18g/* s18QZ */+1|0)){
            if(!E(B(_17F/* GHC.Integer.Type.integerLog2IsPowerOf2# */(_18c/* s18Qw */)).b)){
              return 0;
            }else{
              return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_16O/* GHC.Float.$fRealDouble1 */, _18a/* s18Qu */-_18b/* s18Qv */|0);});
            }
          }else{
            return 0;
          }
        }else{
          var _18i/* s18Ri */ = B(_185/* GHC.Integer.Type.shiftRInteger */(_18c/* s18Qw */, _18h/* s18R4 */));
          switch(B(_17X/* GHC.Integer.Type.roundingMode# */(_18c/* s18Qw */, _18h/* s18R4 */-1|0))){
            case 0:
              return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18i/* s18Ri */, _18a/* s18Qu */-_18b/* s18Qv */|0);});
              break;
            case 1:
              if(!(B(_Vw/* GHC.Integer.Type.integerToInt */(_18i/* s18Ri */))&1)){
                return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18i/* s18Ri */, _18a/* s18Qu */-_18b/* s18Qv */|0);});
              }else{
                return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_18i/* s18Ri */, _16O/* GHC.Float.$fRealDouble1 */)), _18a/* s18Qu */-_18b/* s18Qv */|0);});
              }
              break;
            default:
              return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_18i/* s18Ri */, _16O/* GHC.Float.$fRealDouble1 */)), _18a/* s18Qu */-_18b/* s18Qv */|0);});
          }
        }
      }else{
        return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18c/* s18Qw */, (_18a/* s18Qu */-_18b/* s18Qv */|0)-_18h/* s18R4 */|0);});
      }
    }else{
      if(_18g/* s18QZ */>=_18b/* s18Qv */){
        var _18j/* s18Rx */ = B(_185/* GHC.Integer.Type.shiftRInteger */(_18c/* s18Qw */, (_18g/* s18QZ */+1|0)-_18b/* s18Qv */|0));
        switch(B(_17X/* GHC.Integer.Type.roundingMode# */(_18c/* s18Qw */, _18g/* s18QZ */-_18b/* s18Qv */|0))){
          case 0:
            return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18j/* s18Rx */, ((_18g/* s18QZ */-_18f/* s18Qz */|0)+1|0)-_18b/* s18Qv */|0);});
            break;
          case 2:
            return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_18j/* s18Rx */, _16O/* GHC.Float.$fRealDouble1 */)), ((_18g/* s18QZ */-_18f/* s18Qz */|0)+1|0)-_18b/* s18Qv */|0);});
            break;
          default:
            if(!(B(_Vw/* GHC.Integer.Type.integerToInt */(_18j/* s18Rx */))&1)){
              return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18j/* s18Rx */, ((_18g/* s18QZ */-_18f/* s18Qz */|0)+1|0)-_18b/* s18Qv */|0);});
            }else{
              return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(B(_TH/* GHC.Integer.Type.plusInteger */(_18j/* s18Rx */, _16O/* GHC.Float.$fRealDouble1 */)), ((_18g/* s18QZ */-_18f/* s18Qz */|0)+1|0)-_18b/* s18Qv */|0);});
            }
        }
      }else{
        return new F(function(){return _171/* GHC.Integer.Type.encodeFloatInteger */(_18c/* s18Qw */,  -_18f/* s18Qz */);});
      }
    }
  }else{
    var _18k/* s18QD */ = B(_17w/* GHC.Integer.Type.integerLog2# */(_18c/* s18Qw */))-_18f/* s18Qz */|0,
    _18l/* s18QE */ = function(_18m/* s18QF */){
      var _18n/* s18QG */ = function(_18o/* s18QH */, _18p/* s18QI */){
        if(!B(_Vz/* GHC.Integer.Type.leInteger */(B(_17f/* GHC.Integer.Type.shiftLInteger */(_18p/* s18QI */, _18b/* s18Qv */)), _18o/* s18QH */))){
          return new F(function(){return _17j/* GHC.Float.$w$j */(_18m/* s18QF */-_18b/* s18Qv */|0, _18o/* s18QH */, _18p/* s18QI */);});
        }else{
          return new F(function(){return _17j/* GHC.Float.$w$j */((_18m/* s18QF */-_18b/* s18Qv */|0)+1|0, _18o/* s18QH */, B(_17f/* GHC.Integer.Type.shiftLInteger */(_18p/* s18QI */, 1)));});
        }
      };
      if(_18m/* s18QF */>=_18b/* s18Qv */){
        if(_18m/* s18QF */!=_18b/* s18Qv */){
          return new F(function(){return _18n/* s18QG */(_18c/* s18Qw */, new T(function(){
            return B(_17f/* GHC.Integer.Type.shiftLInteger */(_18d/* s18Qx */, _18m/* s18QF */-_18b/* s18Qv */|0));
          }));});
        }else{
          return new F(function(){return _18n/* s18QG */(_18c/* s18Qw */, _18d/* s18Qx */);});
        }
      }else{
        return new F(function(){return _18n/* s18QG */(new T(function(){
          return B(_17f/* GHC.Integer.Type.shiftLInteger */(_18c/* s18Qw */, _18b/* s18Qv */-_18m/* s18QF */|0));
        }), _18d/* s18Qx */);});
      }
    };
    if(_18a/* s18Qu */>_18k/* s18QD */){
      return new F(function(){return _18l/* s18QE */(_18a/* s18Qu */);});
    }else{
      return new F(function(){return _18l/* s18QE */(_18k/* s18QD */);});
    }
  }
},
_18q/* rationalToFloat1 */ = new T(function(){
  return 0/0;
}),
_18r/* rationalToFloat2 */ = new T(function(){
  return -1/0;
}),
_18s/* rationalToFloat3 */ = new T(function(){
  return 1/0;
}),
_18t/* rationalToFloat4 */ = 0,
_18u/* rationalToFloat */ = function(_18v/* s199U */, _18w/* s199V */){
  if(!B(_14f/* GHC.Integer.Type.eqInteger */(_18w/* s199V */, _17e/* GHC.Float.rationalToDouble5 */))){
    if(!B(_14f/* GHC.Integer.Type.eqInteger */(_18v/* s199U */, _17e/* GHC.Float.rationalToDouble5 */))){
      if(!B(_15o/* GHC.Integer.Type.ltInteger */(_18v/* s199U */, _17e/* GHC.Float.rationalToDouble5 */))){
        return new F(function(){return _189/* GHC.Float.$w$sfromRat''1 */(-1021, 53, _18v/* s199U */, _18w/* s199V */);});
      }else{
        return  -B(_189/* GHC.Float.$w$sfromRat''1 */(-1021, 53, B(_TR/* GHC.Integer.Type.negateInteger */(_18v/* s199U */)), _18w/* s199V */));
      }
    }else{
      return E(_18t/* GHC.Float.rationalToFloat4 */);
    }
  }else{
    return (!B(_14f/* GHC.Integer.Type.eqInteger */(_18v/* s199U */, _17e/* GHC.Float.rationalToDouble5 */))) ? (!B(_15o/* GHC.Integer.Type.ltInteger */(_18v/* s199U */, _17e/* GHC.Float.rationalToDouble5 */))) ? E(_18s/* GHC.Float.rationalToFloat3 */) : E(_18r/* GHC.Float.rationalToFloat2 */) : E(_18q/* GHC.Float.rationalToFloat1 */);
  }
},
_18x/* $fReadFloat_$sconvertFrac */ = function(_18y/* s1vio */){
  var _18z/* s1vip */ = E(_18y/* s1vio */);
  switch(_18z/* s1vip */._){
    case 3:
      var _18A/* s1viq */ = _18z/* s1vip */.a;
      return (!B(_J9/* GHC.Base.eqString */(_18A/* s1viq */, _13w/* GHC.Read.$fReadDouble8 */))) ? (!B(_J9/* GHC.Base.eqString */(_18A/* s1viq */, _13v/* GHC.Read.$fReadDouble7 */))) ? E(_16L/* Text.ParserCombinators.ReadPrec.pfail1 */) : E(_13C/* GHC.Read.$fReadFloat5 */) : E(_13y/* GHC.Read.$fReadFloat3 */);
    case 5:
      var _18B/* s1viu */ = B(_16v/* Text.Read.Lex.$wnumberToRangedRational */(_13G/* GHC.Float.$fRealFloatDouble3 */, _13F/* GHC.Float.$fRealFloatDouble2 */, _18z/* s1vip */.a));
      if(!_18B/* s1viu */._){
        return E(_13y/* GHC.Read.$fReadFloat3 */);
      }else{
        var _18C/* s1viw */ = new T(function(){
          var _18D/* s1vix */ = E(_18B/* s1viu */.a);
          return B(_18u/* GHC.Float.rationalToFloat */(_18D/* s1vix */.a, _18D/* s1vix */.b));
        });
        return function(_18E/* s1viA */, _18F/* s1viB */){
          return new F(function(){return A1(_18F/* s1viB */,_18C/* s1viw */);});
        };
      }
      break;
    default:
      return E(_16L/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_18G/* readEither5 */ = function(_18H/* s2Rfe */){
  var _18I/* s2Rfg */ = function(_18J/* s2Rfh */){
    return E(new T2(3,_18H/* s2Rfe */,_RN/* Text.ParserCombinators.ReadP.Fail */));
  };
  return new T1(1,function(_18K/* s2Rfi */){
    return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_18K/* s2Rfi */, _18I/* s2Rfg */);});
  });
},
_18L/* updateElementValue1 */ = new T(function(){
  return B(A3(_13a/* GHC.Read.$fReadFloat7 */,_18x/* GHC.Read.$fReadFloat_$sconvertFrac */, _12F/* Text.ParserCombinators.ReadPrec.minPrec */, _18G/* Text.Read.readEither5 */));
}),
_18M/* updateElementValue */ = function(_18N/* sa0J */, _18O/* sa0K */){
  var _18P/* sa0L */ = E(_18N/* sa0J */);
  switch(_18P/* sa0L */._){
    case 1:
      return new T4(1,_18P/* sa0L */.a,_18O/* sa0K */,_18P/* sa0L */.c,_18P/* sa0L */.d);
    case 2:
      return new T4(2,_18P/* sa0L */.a,_18O/* sa0K */,_18P/* sa0L */.c,_18P/* sa0L */.d);
    case 3:
      return new T4(3,_18P/* sa0L */.a,_18O/* sa0K */,_18P/* sa0L */.c,_18P/* sa0L */.d);
    case 4:
      return new T5(4,_18P/* sa0L */.a,new T(function(){
        var _18Q/* sa14 */ = B(_Pr/* Text.Read.readEither6 */(B(_Py/* Text.ParserCombinators.ReadP.run */(_18L/* FormEngine.FormElement.Updating.updateElementValue1 */, _18O/* sa0K */))));
        if(!_18Q/* sa14 */._){
          return __Z/* EXTERNAL */;
        }else{
          if(!E(_18Q/* sa14 */.b)._){
            return new T1(1,_18Q/* sa14 */.a);
          }else{
            return __Z/* EXTERNAL */;
          }
        }
      }),_18P/* sa0L */.c,_18P/* sa0L */.d,_18P/* sa0L */.e);
    case 6:
      var _18R/* sa1B */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_18S/* sa1f */){
          var _18T/* sa1g */ = E(_18S/* sa1f */);
          if(!_18T/* sa1g */._){
            var _18U/* sa1j */ = E(_18T/* sa1g */.a);
            return (_18U/* sa1j */._==0) ? (!B(_J9/* GHC.Base.eqString */(_18U/* sa1j */.a, _18O/* sa0K */))) ? new T2(0,_18U/* sa1j */,_2G/* GHC.Types.False */) : new T2(0,_18U/* sa1j */,_8n/* GHC.Types.True */) : (!B(_J9/* GHC.Base.eqString */(_18U/* sa1j */.b, _18O/* sa0K */))) ? new T2(0,_18U/* sa1j */,_2G/* GHC.Types.False */) : new T2(0,_18U/* sa1j */,_8n/* GHC.Types.True */);
          }else{
            var _18V/* sa1s */ = _18T/* sa1g */.c,
            _18W/* sa1t */ = E(_18T/* sa1g */.a);
            return (_18W/* sa1t */._==0) ? (!B(_J9/* GHC.Base.eqString */(_18W/* sa1t */.a, _18O/* sa0K */))) ? new T3(1,_18W/* sa1t */,_2G/* GHC.Types.False */,_18V/* sa1s */) : new T3(1,_18W/* sa1t */,_8n/* GHC.Types.True */,_18V/* sa1s */) : (!B(_J9/* GHC.Base.eqString */(_18W/* sa1t */.b, _18O/* sa0K */))) ? new T3(1,_18W/* sa1t */,_2G/* GHC.Types.False */,_18V/* sa1s */) : new T3(1,_18W/* sa1t */,_8n/* GHC.Types.True */,_18V/* sa1s */);
          }
        }, _18P/* sa0L */.b));
      });
      return new T4(6,_18P/* sa0L */.a,_18R/* sa1B */,_18P/* sa0L */.c,_18P/* sa0L */.d);
    case 7:
      return new T4(7,_18P/* sa0L */.a,new T(function(){
        if(!B(_J9/* GHC.Base.eqString */(_18O/* sa0K */, _I/* GHC.Types.[] */))){
          return new T1(1,_18O/* sa0K */);
        }else{
          return __Z/* EXTERNAL */;
        }
      }),_18P/* sa0L */.c,_18P/* sa0L */.d);
    default:
      return E(_18P/* sa0L */);
  }
},
_18X/* identity2elementUpdated2 */ = function(_18Y/* sa1I */, _/* EXTERNAL */){
  var _18Z/* sa1K */ = E(_18Y/* sa1I */);
  if(_18Z/* sa1K */._==4){
    var _190/* sa26 */ = _18Z/* sa1K */.a,
    _191/* sa29 */ = _18Z/* sa1K */.d,
    _192/* sa2a */ = _18Z/* sa1K */.e,
    _193/* sa2c */ = B(_PJ/* FormEngine.JQuery.selectByName1 */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_18Z/* sa1K */)), _/* EXTERNAL */)),
    _194/* sa2k */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_193/* sa2c */)),
    _195/* sa2z */ = B(_Pj/* FormEngine.JQuery.getRadioValue1 */(new T(function(){
      return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4r/* FormEngine.FormItem.fiDescriptor */(_190/* sa26 */)).b)), _Pq/* FormEngine.FormItem.nfiUnitId1 */));
    },1), _/* EXTERNAL */));
    return new T(function(){
      var _196/* sa2C */ = new T(function(){
        var _197/* sa2E */ = String/* EXTERNAL */(_194/* sa2k */);
        return fromJSStr/* EXTERNAL */(_197/* sa2E */);
      }),
      _198/* sa2K */ = function(_199/* sa2L */){
        return new T5(4,_190/* sa26 */,new T(function(){
          var _19a/* sa2N */ = B(_Pr/* Text.Read.readEither6 */(B(_Py/* Text.ParserCombinators.ReadP.run */(_18L/* FormEngine.FormElement.Updating.updateElementValue1 */, _196/* sa2C */))));
          if(!_19a/* sa2N */._){
            return __Z/* EXTERNAL */;
          }else{
            if(!E(_19a/* sa2N */.b)._){
              return new T1(1,_19a/* sa2N */.a);
            }else{
              return __Z/* EXTERNAL */;
            }
          }
        }),_2o/* GHC.Base.Nothing */,_191/* sa29 */,_192/* sa2a */);
      };
      if(!B(_J9/* GHC.Base.eqString */(_195/* sa2z */, _Pp/* FormEngine.FormElement.Updating.lvl1 */))){
        var _19b/* sa2V */ = E(_195/* sa2z */);
        if(!_19b/* sa2V */._){
          return B(_198/* sa2K */(_/* EXTERNAL */));
        }else{
          return new T5(4,_190/* sa26 */,new T(function(){
            var _19c/* sa2Z */ = B(_Pr/* Text.Read.readEither6 */(B(_Py/* Text.ParserCombinators.ReadP.run */(_18L/* FormEngine.FormElement.Updating.updateElementValue1 */, _196/* sa2C */))));
            if(!_19c/* sa2Z */._){
              return __Z/* EXTERNAL */;
            }else{
              if(!E(_19c/* sa2Z */.b)._){
                return new T1(1,_19c/* sa2Z */.a);
              }else{
                return __Z/* EXTERNAL */;
              }
            }
          }),new T1(1,_19b/* sa2V */),_191/* sa29 */,_192/* sa2a */);
        }
      }else{
        return B(_198/* sa2K */(_/* EXTERNAL */));
      }
    });
  }else{
    var _19d/* sa1M */ = B(_PJ/* FormEngine.JQuery.selectByName1 */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_18Z/* sa1K */)), _/* EXTERNAL */)),
    _19e/* sa1U */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_19d/* sa1M */));
    return new T(function(){
      return B(_18M/* FormEngine.FormElement.Updating.updateElementValue */(_18Z/* sa1K */, new T(function(){
        var _19f/* sa1Y */ = String/* EXTERNAL */(_19e/* sa1U */);
        return fromJSStr/* EXTERNAL */(_19f/* sa1Y */);
      })));
    });
  }
},
_19g/* identity2elementUpdated3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" does not exist"));
}),
_19h/* identity2elementUpdated4 */ = new T2(1,_Ma/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_19i/* $wa */ = function(_19j/* sa3H */, _19k/* sa3I */, _/* EXTERNAL */){
  var _19l/* sa3K */ = B(_P7/* FormEngine.FormElement.Updating.identity2element' */(_19j/* sa3H */, _19k/* sa3I */));
  if(!_19l/* sa3K */._){
    var _19m/* sa3N */ = new T(function(){
      return B(_12/* GHC.Base.++ */(new T2(1,_Ma/* GHC.Show.shows5 */,new T(function(){
        return B(_NK/* GHC.Show.showLitString */(_19j/* sa3H */, _19h/* FormEngine.FormElement.Updating.identity2elementUpdated4 */));
      })), _19g/* FormEngine.FormElement.Updating.identity2elementUpdated3 */));
    }),
    _19n/* sa3P */ = B(_5Q/* FormEngine.JQuery.errorIO1 */(B(unAppCStr/* EXTERNAL */("identity2elementUpdated: element with identity=", _19m/* sa3N */)), _/* EXTERNAL */));
    return _2o/* GHC.Base.Nothing */;
  }else{
    var _19o/* sa3T */ = B(_18X/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_19l/* sa3K */.a, _/* EXTERNAL */));
    return new T1(1,_19o/* sa3T */);
  }
},
_19p/* setVal2 */ = "(function (val, jq) { jq.val(val).change(); return jq; })",
_19q/* $wa35 */ = function(_19r/* stWR */, _19s/* stWS */, _/* EXTERNAL */){
  var _19t/* stX2 */ = eval/* EXTERNAL */(E(_19p/* FormEngine.JQuery.setVal2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_19t/* stX2 */), toJSStr/* EXTERNAL */(E(_19r/* stWR */)), _19s/* stWS */);});
},
_19u/* $fExceptionRecSelError_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RecSelError"));
}),
_19v/* $fExceptionRecSelError_wild */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_PM/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_PN/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_19u/* Control.Exception.Base.$fExceptionRecSelError_ww4 */),
_19w/* $fExceptionRecSelError2 */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_19v/* Control.Exception.Base.$fExceptionRecSelError_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_19x/* $fExceptionRecSelError1 */ = function(_19y/* s4nv0 */){
  return E(_19w/* Control.Exception.Base.$fExceptionRecSelError2 */);
},
_19z/* $fExceptionRecSelError_$cfromException */ = function(_19A/* s4nvr */){
  var _19B/* s4nvs */ = E(_19A/* s4nvr */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_19B/* s4nvs */.a)), _19x/* Control.Exception.Base.$fExceptionRecSelError1 */, _19B/* s4nvs */.b);});
},
_19C/* $fExceptionRecSelError_$cshow */ = function(_19D/* s4nvj */){
  return E(E(_19D/* s4nvj */).a);
},
_19E/* $fExceptionRecSelError_$ctoException */ = function(_PZ/* B1 */){
  return new T2(0,_19F/* Control.Exception.Base.$fExceptionRecSelError */,_PZ/* B1 */);
},
_19G/* $fShowRecSelError1 */ = function(_19H/* s4nqO */, _19I/* s4nqP */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_19H/* s4nqO */).a, _19I/* s4nqP */);});
},
_19J/* $fShowRecSelError_$cshowList */ = function(_19K/* s4nvh */, _19L/* s4nvi */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_19G/* Control.Exception.Base.$fShowRecSelError1 */, _19K/* s4nvh */, _19L/* s4nvi */);});
},
_19M/* $fShowRecSelError_$cshowsPrec */ = function(_19N/* s4nvm */, _19O/* s4nvn */, _19P/* s4nvo */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_19O/* s4nvn */).a, _19P/* s4nvo */);});
},
_19Q/* $fShowRecSelError */ = new T3(0,_19M/* Control.Exception.Base.$fShowRecSelError_$cshowsPrec */,_19C/* Control.Exception.Base.$fExceptionRecSelError_$cshow */,_19J/* Control.Exception.Base.$fShowRecSelError_$cshowList */),
_19F/* $fExceptionRecSelError */ = new T(function(){
  return new T5(0,_19x/* Control.Exception.Base.$fExceptionRecSelError1 */,_19Q/* Control.Exception.Base.$fShowRecSelError */,_19E/* Control.Exception.Base.$fExceptionRecSelError_$ctoException */,_19z/* Control.Exception.Base.$fExceptionRecSelError_$cfromException */,_19C/* Control.Exception.Base.$fExceptionRecSelError_$cshow */);
}),
_19R/* recSelError */ = function(_19S/* s4nwW */){
  var _19T/* s4nwY */ = new T(function(){
    return B(unAppCStr/* EXTERNAL */("No match in record selector ", new T(function(){
      return B(unCStr/* EXTERNAL */(_19S/* s4nwW */));
    })));
  });
  return new F(function(){return _Qg/* GHC.Exception.throw1 */(new T1(0,_19T/* s4nwY */), _19F/* Control.Exception.Base.$fExceptionRecSelError */);});
},
_19U/* neMaybeValue1 */ = new T(function(){
  return B(_19R/* Control.Exception.Base.recSelError */("neMaybeValue"));
}),
_19V/* $wgo */ = function(_19W/* sa4c */, _19X/* sa4d */){
  while(1){
    var _19Y/* sa4e */ = E(_19W/* sa4c */);
    if(!_19Y/* sa4e */._){
      return E(_19X/* sa4d */);
    }else{
      var _19Z/* sa4g */ = _19Y/* sa4e */.b,
      _1a0/* sa4h */ = E(_19Y/* sa4e */.a);
      if(_1a0/* sa4h */._==4){
        var _1a1/* sa4o */ = E(_1a0/* sa4h */.b);
        if(!_1a1/* sa4o */._){
          _19W/* sa4c */ = _19Z/* sa4g */;
          continue;
        }else{
          var _1a2/*  sa4d */ = _19X/* sa4d */+E(_1a1/* sa4o */.a);
          _19W/* sa4c */ = _19Z/* sa4g */;
          _19X/* sa4d */ = _1a2/*  sa4d */;
          continue;
        }
      }else{
        return E(_19U/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
      }
    }
  }
},
_1a3/* numberElem2TB1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_1a4/* numberElem2TB2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_1a5/* numberElem2TB3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_1a6/* numberElem2TB4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_1a7/* numberElem2TB */ = function(_1a8/* s70l */){
  var _1a9/* s70m */ = E(_1a8/* s70l */);
  if(_1a9/* s70m */._==4){
    var _1aa/* s70o */ = _1a9/* s70m */.b,
    _1ab/* s70s */ = E(_1a9/* s70m */.c);
    if(!_1ab/* s70s */._){
      return __Z/* EXTERNAL */;
    }else{
      var _1ac/* s70t */ = _1ab/* s70s */.a;
      if(!B(_J9/* GHC.Base.eqString */(_1ac/* s70t */, _1a6/* FormEngine.FormElement.FormElement.numberElem2TB4 */))){
        if(!B(_J9/* GHC.Base.eqString */(_1ac/* s70t */, _1a5/* FormEngine.FormElement.FormElement.numberElem2TB3 */))){
          if(!B(_J9/* GHC.Base.eqString */(_1ac/* s70t */, _1a4/* FormEngine.FormElement.FormElement.numberElem2TB2 */))){
            return (!B(_J9/* GHC.Base.eqString */(_1ac/* s70t */, _1a3/* FormEngine.FormElement.FormElement.numberElem2TB1 */))) ? __Z/* EXTERNAL */ : E(_1aa/* s70o */);
          }else{
            var _1ad/* s70y */ = E(_1aa/* s70o */);
            return (_1ad/* s70y */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
              return E(_1ad/* s70y */.a)*1000;
            }));
          }
        }else{
          var _1ae/* s70E */ = E(_1aa/* s70o */);
          return (_1ae/* s70E */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
            return E(_1ae/* s70E */.a)*1.0e-6;
          }));
        }
      }else{
        var _1af/* s70K */ = E(_1aa/* s70o */);
        return (_1af/* s70K */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
          return E(_1af/* s70K */.a)*1.0e-3;
        }));
      }
    }
  }else{
    return __Z/* EXTERNAL */;
  }
},
_1ag/* $wgo1 */ = function(_1ah/* sa4z */, _1ai/* sa4A */){
  while(1){
    var _1aj/* sa4B */ = E(_1ah/* sa4z */);
    if(!_1aj/* sa4B */._){
      return E(_1ai/* sa4A */);
    }else{
      var _1ak/* sa4D */ = _1aj/* sa4B */.b,
      _1al/* sa4E */ = B(_1a7/* FormEngine.FormElement.FormElement.numberElem2TB */(_1aj/* sa4B */.a));
      if(!_1al/* sa4E */._){
        _1ah/* sa4z */ = _1ak/* sa4D */;
        continue;
      }else{
        var _1am/*  sa4A */ = _1ai/* sa4A */+E(_1al/* sa4E */.a);
        _1ah/* sa4z */ = _1ak/* sa4D */;
        _1ai/* sa4A */ = _1am/*  sa4A */;
        continue;
      }
    }
  }
},
_1an/* disableJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("true"));
}),
_1ao/* disableJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("readonly"));
}),
_1ap/* disableJq6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#eee"));
}),
_1aq/* disableJq7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("background-color"));
}),
_1ar/* go */ = function(_1as/* sa46 */){
  while(1){
    var _1at/* sa47 */ = E(_1as/* sa46 */);
    if(!_1at/* sa47 */._){
      return false;
    }else{
      if(!E(_1at/* sa47 */.a)._){
        return true;
      }else{
        _1as/* sa46 */ = _1at/* sa47 */.b;
        continue;
      }
    }
  }
},
_1au/* go1 */ = function(_1av/* sa4t */){
  while(1){
    var _1aw/* sa4u */ = E(_1av/* sa4t */);
    if(!_1aw/* sa4u */._){
      return false;
    }else{
      if(!E(_1aw/* sa4u */.a)._){
        return true;
      }else{
        _1av/* sa4t */ = _1aw/* sa4u */.b;
        continue;
      }
    }
  }
},
_1ax/* selectIn2 */ = "(function (elId, context) { return $(elId, context); })",
_1ay/* $wa18 */ = function(_1az/* su0l */, _1aA/* su0m */, _/* EXTERNAL */){
  var _1aB/* su0w */ = eval/* EXTERNAL */(E(_1ax/* FormEngine.JQuery.selectIn2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_1aB/* su0w */), toJSStr/* EXTERNAL */(E(_1az/* su0l */)), _1aA/* su0m */);});
},
_1aC/* flagPlaceId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_flagPlaceId"));
}),
_1aD/* inputFieldUpdate3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".validity-flag"));
}),
_1aE/* inputFieldUpdate4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1aF/* invalidImg */ = function(_1aG/* sa0b */){
  return E(E(_1aG/* sa0b */).c);
},
_1aH/* removeJq_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { var p = jq.parent(); jq.remove(); return p; })");
}),
_1aI/* validImg */ = function(_1aJ/* sa0p */){
  return E(E(_1aJ/* sa0p */).b);
},
_1aK/* inputFieldUpdate2 */ = function(_1aL/* s9ZP */, _1aM/* s9ZQ */, _1aN/* s9ZR */, _/* EXTERNAL */){
  var _1aO/* s9ZW */ = B(_56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1aE/* FormEngine.FormElement.Updating.inputFieldUpdate4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1aL/* s9ZP */)), _1aC/* FormEngine.FormElement.Identifiers.flagPlaceId1 */));
  },1))), _/* EXTERNAL */)),
  _1aP/* s9ZZ */ = E(_1aO/* s9ZW */),
  _1aQ/* sa01 */ = B(_1ay/* FormEngine.JQuery.$wa18 */(_1aD/* FormEngine.FormElement.Updating.inputFieldUpdate3 */, _1aP/* s9ZZ */, _/* EXTERNAL */)),
  _1aR/* sa09 */ = __app1/* EXTERNAL */(E(_1aH/* FormEngine.JQuery.removeJq_f1 */), E(_1aQ/* sa01 */));
  if(!E(_1aN/* s9ZR */)){
    if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1aL/* s9ZP */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _1aS/* sa0q */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_1aF/* FormEngine.FormContext.invalidImg */(_1aM/* s9ZQ */)), _1aP/* s9ZZ */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }else{
    if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1aL/* s9ZP */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _1aT/* sa0G */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_1aI/* FormEngine.FormContext.validImg */(_1aM/* s9ZQ */)), _1aP/* s9ZZ */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }
},
_1aU/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rule application did not unify: "));
}),
_1aV/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" @"));
}),
_1aW/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid operand in "));
}),
_1aX/* selectByIdentity2 */ = "(function (identity) { return $(\'[identity=\"\' + identity + \'\"]\'); })",
_1aY/* selectByIdentity1 */ = function(_1aZ/* stN0 */, _/* EXTERNAL */){
  var _1b0/* stNa */ = eval/* EXTERNAL */(E(_1aX/* FormEngine.JQuery.selectByIdentity2 */));
  return new F(function(){return __app1/* EXTERNAL */(E(_1b0/* stNa */), toJSStr/* EXTERNAL */(E(_1aZ/* stN0 */)));});
},
_1b1/* applyRule1 */ = function(_1b2/* sa4J */, _1b3/* sa4K */, _1b4/* sa4L */, _/* EXTERNAL */){
  var _1b5/* sa4N */ = function(_/* EXTERNAL */){
    var _1b6/* sa4P */ = E(_1b4/* sa4L */);
    switch(_1b6/* sa4P */._){
      case 2:
        var _1b7/* sa4X */ = B(_1aY/* FormEngine.JQuery.selectByIdentity1 */(_1b6/* sa4P */.a, _/* EXTERNAL */)),
        _1b8/* sa55 */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_1b7/* sa4X */)),
        _1b9/* sa58 */ = B(_1aY/* FormEngine.JQuery.selectByIdentity1 */(_1b6/* sa4P */.b, _/* EXTERNAL */)),
        _1ba/* sa5c */ = String/* EXTERNAL */(_1b8/* sa55 */),
        _1bb/* sa5l */ = B(_19q/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_1ba/* sa5c */), E(_1b9/* sa58 */), _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 3:
        var _1bc/* sa5p */ = B(_PJ/* FormEngine.JQuery.selectByName1 */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1b2/* sa4J */)), _/* EXTERNAL */)),
        _1bd/* sa5s */ = E(_1bc/* sa5p */),
        _1be/* sa5u */ = B(_43/* FormEngine.JQuery.$wa2 */(_1aq/* FormEngine.JQuery.disableJq7 */, _1ap/* FormEngine.JQuery.disableJq6 */, _1bd/* sa5s */, _/* EXTERNAL */)),
        _1bf/* sa5x */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ao/* FormEngine.JQuery.disableJq3 */, _1an/* FormEngine.JQuery.disableJq2 */, _1bd/* sa5s */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 4:
        var _1bg/* sa5B */ = B(_18X/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_1b2/* sa4J */, _/* EXTERNAL */)),
        _1bh/* sa5E */ = E(_1bg/* sa5B */);
        if(_1bh/* sa5E */._==4){
          var _1bi/* sa5L */ = E(_1bh/* sa5E */.b);
          if(!_1bi/* sa5L */._){
            return new F(function(){return _1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1bh/* sa5E */, _1b3/* sa4K */, _2G/* GHC.Types.False */, _/* EXTERNAL */);});
          }else{
            return new F(function(){return _1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1bh/* sa5E */, _1b3/* sa4K */, new T(function(){
              return B(A1(_1b6/* sa4P */.a,_1bi/* sa5L */.a));
            },1), _/* EXTERNAL */);});
          }
        }else{
          return E(_19U/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
        }
        break;
      default:
        var _1bj/* sa4T */ = new T(function(){
          var _1bk/* sa4S */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_1aV/* FormEngine.FormElement.Updating.lvl3 */, new T(function(){
              return B(_LY/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_1b2/* sa4J */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(B(_OY/* FormEngine.FormItem.$fShowFormRule_$cshow */(_1b6/* sa4P */)), _1bk/* sa4S */));
        },1);
        return new F(function(){return _5Q/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_1aU/* FormEngine.FormElement.Updating.lvl2 */, _1bj/* sa4T */)), _/* EXTERNAL */);});
    }
  };
  if(E(_1b2/* sa4J */)._==4){
    var _1bl/* sa5U */ = E(_1b4/* sa4L */);
    switch(_1bl/* sa5U */._){
      case 0:
        var _1bm/* sa5X */ = function(_/* EXTERNAL */, _1bn/* sa5Z */){
          if(!B(_1ar/* FormEngine.FormElement.Updating.go */(_1bn/* sa5Z */))){
            var _1bo/* sa61 */ = B(_1aY/* FormEngine.JQuery.selectByIdentity1 */(_1bl/* sa5U */.b, _/* EXTERNAL */)),
            _1bp/* sa67 */ = jsShow/* EXTERNAL */(B(_19V/* FormEngine.FormElement.Updating.$wgo */(B(_5I/* Data.Maybe.catMaybes1 */(_1bn/* sa5Z */)), 0))),
            _1bq/* sa6e */ = B(_19q/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_1bp/* sa67 */), E(_1bo/* sa61 */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _1br/* sa6j */ = B(_5Q/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_1aW/* FormEngine.FormElement.Updating.lvl4 */, new T(function(){
              return B(_OY/* FormEngine.FormItem.$fShowFormRule_$cshow */(_1bl/* sa5U */));
            },1))), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        },
        _1bs/* sa6m */ = E(_1bl/* sa5U */.a);
        if(!_1bs/* sa6m */._){
          return new F(function(){return _1bm/* sa5X */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _1bt/* sa6q */ = E(_1b3/* sa4K */).a,
          _1bu/* sa6v */ = B(_19i/* FormEngine.FormElement.Updating.$wa */(_1bs/* sa6m */.a, _1bt/* sa6q */, _/* EXTERNAL */)),
          _1bv/* sa6y */ = function(_1bw/* sa6z */, _/* EXTERNAL */){
            var _1bx/* sa6B */ = E(_1bw/* sa6z */);
            if(!_1bx/* sa6B */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _1by/* sa6E */ = B(_19i/* FormEngine.FormElement.Updating.$wa */(_1bx/* sa6B */.a, _1bt/* sa6q */, _/* EXTERNAL */)),
              _1bz/* sa6H */ = B(_1bv/* sa6y */(_1bx/* sa6B */.b, _/* EXTERNAL */));
              return new T2(1,_1by/* sa6E */,_1bz/* sa6H */);
            }
          },
          _1bA/* sa6L */ = B(_1bv/* sa6y */(_1bs/* sa6m */.b, _/* EXTERNAL */));
          return new F(function(){return _1bm/* sa5X */(_/* EXTERNAL */, new T2(1,_1bu/* sa6v */,_1bA/* sa6L */));});
        }
        break;
      case 1:
        var _1bB/* sa6R */ = function(_/* EXTERNAL */, _1bC/* sa6T */){
          if(!B(_1au/* FormEngine.FormElement.Updating.go1 */(_1bC/* sa6T */))){
            var _1bD/* sa6V */ = B(_1aY/* FormEngine.JQuery.selectByIdentity1 */(_1bl/* sa5U */.b, _/* EXTERNAL */)),
            _1bE/* sa71 */ = jsShow/* EXTERNAL */(B(_1ag/* FormEngine.FormElement.Updating.$wgo1 */(B(_5I/* Data.Maybe.catMaybes1 */(_1bC/* sa6T */)), 0))),
            _1bF/* sa78 */ = B(_19q/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_1bE/* sa71 */), E(_1bD/* sa6V */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            return _0/* GHC.Tuple.() */;
          }
        },
        _1bG/* sa7b */ = E(_1bl/* sa5U */.a);
        if(!_1bG/* sa7b */._){
          return new F(function(){return _1bB/* sa6R */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _1bH/* sa7f */ = E(_1b3/* sa4K */).a,
          _1bI/* sa7k */ = B(_19i/* FormEngine.FormElement.Updating.$wa */(_1bG/* sa7b */.a, _1bH/* sa7f */, _/* EXTERNAL */)),
          _1bJ/* sa7n */ = function(_1bK/* sa7o */, _/* EXTERNAL */){
            var _1bL/* sa7q */ = E(_1bK/* sa7o */);
            if(!_1bL/* sa7q */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _1bM/* sa7t */ = B(_19i/* FormEngine.FormElement.Updating.$wa */(_1bL/* sa7q */.a, _1bH/* sa7f */, _/* EXTERNAL */)),
              _1bN/* sa7w */ = B(_1bJ/* sa7n */(_1bL/* sa7q */.b, _/* EXTERNAL */));
              return new T2(1,_1bM/* sa7t */,_1bN/* sa7w */);
            }
          },
          _1bO/* sa7A */ = B(_1bJ/* sa7n */(_1bG/* sa7b */.b, _/* EXTERNAL */));
          return new F(function(){return _1bB/* sa6R */(_/* EXTERNAL */, new T2(1,_1bI/* sa7k */,_1bO/* sa7A */));});
        }
        break;
      default:
        return new F(function(){return _1b5/* sa4N */(_/* EXTERNAL */);});
    }
  }else{
    return new F(function(){return _1b5/* sa4N */(_/* EXTERNAL */);});
  }
},
_1bP/* applyRules1 */ = function(_1bQ/* sa7E */, _1bR/* sa7F */, _/* EXTERNAL */){
  var _1bS/* sa7S */ = function(_1bT/* sa7T */, _/* EXTERNAL */){
    while(1){
      var _1bU/* sa7V */ = E(_1bT/* sa7T */);
      if(!_1bU/* sa7V */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1bV/* sa7Y */ = B(_1b1/* FormEngine.FormElement.Updating.applyRule1 */(_1bQ/* sa7E */, _1bR/* sa7F */, _1bU/* sa7V */.a, _/* EXTERNAL */));
        _1bT/* sa7T */ = _1bU/* sa7V */.b;
        continue;
      }
    }
  };
  return new F(function(){return _1bS/* sa7S */(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1bQ/* sa7E */)))).i, _/* EXTERNAL */);});
},
_1bW/* isJust */ = function(_1bX/* s7rZ */){
  return (E(_1bX/* s7rZ */)._==0) ? false : true;
},
_1bY/* nfiUnit1 */ = new T(function(){
  return B(_19R/* Control.Exception.Base.recSelError */("nfiUnit"));
}),
_1bZ/* egElements */ = function(_1c0/* s6H6 */){
  return E(E(_1c0/* s6H6 */).a);
},
_1c1/* go */ = function(_1c2/* saC6 */){
  while(1){
    var _1c3/* saC7 */ = E(_1c2/* saC6 */);
    if(!_1c3/* saC7 */._){
      return true;
    }else{
      if(!E(_1c3/* saC7 */.a)){
        return false;
      }else{
        _1c2/* saC6 */ = _1c3/* saC7 */.b;
        continue;
      }
    }
  }
},
_1c4/* validateElement2 */ = function(_1c5/* saGb */){
  return new F(function(){return _1c1/* FormEngine.FormElement.Validation.go */(B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1c5/* saGb */)));});
},
_1c7/* validateElement3 */ = function(_1c8/* saCe */){
  var _1c9/* saCf */ = E(_1c8/* saCe */);
  if(!_1c9/* saCf */._){
    return true;
  }else{
    return new F(function(){return _1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1c9/* saCf */.c);});
  }
},
_1ca/* validateElement_go */ = function(_1cb/* saBK */){
  while(1){
    var _1cc/* saBL */ = E(_1cb/* saBK */);
    if(!_1cc/* saBL */._){
      return true;
    }else{
      if(!E(_1cc/* saBL */.a)){
        return false;
      }else{
        _1cb/* saBK */ = _1cc/* saBL */.b;
        continue;
      }
    }
  }
},
_1cd/* validateElement_go1 */ = function(_1ce/* saBP */){
  while(1){
    var _1cf/* saBQ */ = E(_1ce/* saBP */);
    if(!_1cf/* saBQ */._){
      return false;
    }else{
      var _1cg/* saBS */ = _1cf/* saBQ */.b,
      _1ch/* saBT */ = E(_1cf/* saBQ */.a);
      if(!_1ch/* saBT */._){
        if(!E(_1ch/* saBT */.b)){
          _1ce/* saBP */ = _1cg/* saBS */;
          continue;
        }else{
          return true;
        }
      }else{
        if(!E(_1ch/* saBT */.b)){
          _1ce/* saBP */ = _1cg/* saBS */;
          continue;
        }else{
          return true;
        }
      }
    }
  }
},
_1ci/* validateElement_go2 */ = function(_1cj/* saC1 */){
  while(1){
    var _1ck/* saC2 */ = E(_1cj/* saC1 */);
    if(!_1ck/* saC2 */._){
      return true;
    }else{
      if(!E(_1ck/* saC2 */.a)){
        return false;
      }else{
        _1cj/* saC1 */ = _1ck/* saC2 */.b;
        continue;
      }
    }
  }
},
_1c6/* go1 */ = function(_1cl/*  saCl */){
  while(1){
    var _1cm/*  go1 */ = B((function(_1cn/* saCl */){
      var _1co/* saCm */ = E(_1cn/* saCl */);
      if(!_1co/* saCm */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1cp/* saCo */ = _1co/* saCm */.b,
        _1cq/* saCp */ = E(_1co/* saCm */.a);
        switch(_1cq/* saCp */._){
          case 0:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cq/* saCp */.b));
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 1:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cq/* saCp */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 2:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cq/* saCp */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 3:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cq/* saCp */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 4:
            var _1cr/* saDy */ = _1cq/* saCp */.a;
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cr/* saDy */)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                var _1cs/* saDO */ = E(_1cq/* saCp */.b);
                if(!_1cs/* saDO */._){
                  return false;
                }else{
                  if(E(_1cs/* saDO */.a)<0){
                    return false;
                  }else{
                    var _1ct/* saDU */ = E(_1cr/* saDy */);
                    if(_1ct/* saDU */._==3){
                      if(E(_1ct/* saDU */.b)._==1){
                        return B(_1bW/* Data.Maybe.isJust */(_1cq/* saCp */.c));
                      }else{
                        return true;
                      }
                    }else{
                      return E(_1bY/* FormEngine.FormItem.nfiUnit1 */);
                    }
                  }
                }
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 5:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8n/* GHC.Types.True */,new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 6:
            var _1cu/* saEg */ = _1cq/* saCp */.a,
            _1cv/* saEh */ = _1cq/* saCp */.b;
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cu/* saEg */)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cu/* saEg */)).h)){
                  return B(_1ci/* FormEngine.FormElement.Validation.validateElement_go2 */(B(_2S/* GHC.Base.map */(_1c7/* FormEngine.FormElement.Validation.validateElement3 */, _1cv/* saEh */))));
                }else{
                  if(!B(_1cd/* FormEngine.FormElement.Validation.validateElement_go1 */(_1cv/* saEh */))){
                    return false;
                  }else{
                    return B(_1ci/* FormEngine.FormElement.Validation.validateElement_go2 */(B(_2S/* GHC.Base.map */(_1c7/* FormEngine.FormElement.Validation.validateElement3 */, _1cv/* saEh */))));
                  }
                }
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 7:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_1bW/* Data.Maybe.isJust */(_1cq/* saCp */.b));
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 8:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cq/* saCp */.b));
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 9:
            return new T2(1,new T(function(){
              if(!E(_1cq/* saCp */.b)){
                return true;
              }else{
                return B(_1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cq/* saCp */.c));
              }
            }),new T(function(){
              return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
            }));
          case 10:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_1ca/* FormEngine.FormElement.Validation.validateElement_go */(B(_2S/* GHC.Base.map */(_1cw/* FormEngine.FormElement.Validation.validateElement1 */, _1cq/* saCp */.b))));
              }),new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          case 11:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8n/* GHC.Types.True */,new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
            break;
          default:
            if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cq/* saCp */.a)).h)){
              _1cl/*  saCl */ = _1cp/* saCo */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8n/* GHC.Types.True */,new T(function(){
                return B(_1c6/* FormEngine.FormElement.Validation.go1 */(_1cp/* saCo */));
              }));
            }
        }
      }
    })(_1cl/*  saCl */));
    if(_1cm/*  go1 */!=__continue/* EXTERNAL */){
      return _1cm/*  go1 */;
    }
  }
},
_1cw/* validateElement1 */ = function(_1cx/* saCb */){
  return new F(function(){return _1c1/* FormEngine.FormElement.Validation.go */(B(_1c6/* FormEngine.FormElement.Validation.go1 */(B(_1bZ/* FormEngine.FormElement.FormElement.egElements */(_1cx/* saCb */)))));});
},
_1cy/* validateElement */ = function(_1cz/* saGd */){
  var _1cA/* saGe */ = E(_1cz/* saGd */);
  switch(_1cA/* saGe */._){
    case 0:
      return new F(function(){return _1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cA/* saGe */.b);});
      break;
    case 1:
      return (!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cA/* saGe */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 2:
      return (!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cA/* saGe */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 3:
      return (!B(_Rt/* GHC.Classes.$fEq[]_$s$c==1 */(_1cA/* saGe */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 4:
      var _1cB/* saGC */ = E(_1cA/* saGe */.b);
      if(!_1cB/* saGC */._){
        return false;
      }else{
        if(E(_1cB/* saGC */.a)<0){
          return false;
        }else{
          var _1cC/* saGI */ = E(_1cA/* saGe */.a);
          if(_1cC/* saGI */._==3){
            if(E(_1cC/* saGI */.b)._==1){
              return new F(function(){return _1bW/* Data.Maybe.isJust */(_1cA/* saGe */.c);});
            }else{
              return true;
            }
          }else{
            return E(_1bY/* FormEngine.FormItem.nfiUnit1 */);
          }
        }
      }
      break;
    case 6:
      var _1cD/* saGP */ = _1cA/* saGe */.b;
      if(!E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1cA/* saGe */.a)).h)){
        return new F(function(){return _1ci/* FormEngine.FormElement.Validation.validateElement_go2 */(B(_2S/* GHC.Base.map */(_1c7/* FormEngine.FormElement.Validation.validateElement3 */, _1cD/* saGP */)));});
      }else{
        if(!B(_1cd/* FormEngine.FormElement.Validation.validateElement_go1 */(_1cD/* saGP */))){
          return false;
        }else{
          return new F(function(){return _1ci/* FormEngine.FormElement.Validation.validateElement_go2 */(B(_2S/* GHC.Base.map */(_1c7/* FormEngine.FormElement.Validation.validateElement3 */, _1cD/* saGP */)));});
        }
      }
      break;
    case 7:
      return new F(function(){return _1bW/* Data.Maybe.isJust */(_1cA/* saGe */.b);});
      break;
    case 8:
      return new F(function(){return _1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cA/* saGe */.b);});
      break;
    case 9:
      if(!E(_1cA/* saGe */.b)){
        return true;
      }else{
        return new F(function(){return _1c4/* FormEngine.FormElement.Validation.validateElement2 */(_1cA/* saGe */.c);});
      }
      break;
    case 10:
      return new F(function(){return _1ca/* FormEngine.FormElement.Validation.validateElement_go */(B(_2S/* GHC.Base.map */(_1cw/* FormEngine.FormElement.Validation.validateElement1 */, _1cA/* saGe */.b)));});
      break;
    default:
      return true;
  }
},
_1cE/* $wa */ = function(_1cF/* sfTI */, _1cG/* sfTJ */, _1cH/* sfTK */, _/* EXTERNAL */){
  var _1cI/* sfTM */ = B(_18X/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_1cF/* sfTI */, _/* EXTERNAL */)),
  _1cJ/* sfTQ */ = B(_1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1cI/* sfTM */, _1cG/* sfTJ */, new T(function(){
    return B(_1cy/* FormEngine.FormElement.Validation.validateElement */(_1cI/* sfTM */));
  },1), _/* EXTERNAL */)),
  _1cK/* sfTT */ = B(_1bP/* FormEngine.FormElement.Updating.applyRules1 */(_1cF/* sfTI */, _1cG/* sfTJ */, _/* EXTERNAL */)),
  _1cL/* sfU0 */ = E(E(_1cH/* sfTK */).b);
  if(!_1cL/* sfU0 */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_1cL/* sfU0 */.a,_1cF/* sfTI */, _1cG/* sfTJ */, _/* EXTERNAL */);});
  }
},
_1cM/* $wa1 */ = function(_1cN/* sfU2 */, _1cO/* sfU3 */, _1cP/* sfU4 */, _/* EXTERNAL */){
  var _1cQ/* sfU6 */ = B(_18X/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_1cN/* sfU2 */, _/* EXTERNAL */)),
  _1cR/* sfUa */ = B(_1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1cQ/* sfU6 */, _1cO/* sfU3 */, new T(function(){
    return B(_1cy/* FormEngine.FormElement.Validation.validateElement */(_1cQ/* sfU6 */));
  },1), _/* EXTERNAL */)),
  _1cS/* sfUd */ = B(_1bP/* FormEngine.FormElement.Updating.applyRules1 */(_1cN/* sfU2 */, _1cO/* sfU3 */, _/* EXTERNAL */)),
  _1cT/* sfUk */ = E(E(_1cP/* sfU4 */).a);
  if(!_1cT/* sfUk */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_1cT/* sfUk */.a,_1cN/* sfU2 */, _1cO/* sfU3 */, _/* EXTERNAL */);});
  }
},
_1cU/* $wa1 */ = function(_1cV/* stTD */, _1cW/* stTE */, _/* EXTERNAL */){
  var _1cX/* stTJ */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _1cW/* stTE */),
  _1cY/* stTP */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _1cX/* stTJ */),
  _1cZ/* stU0 */ = eval/* EXTERNAL */(E(_HN/* FormEngine.JQuery.addClass2 */)),
  _1d0/* stU8 */ = __app2/* EXTERNAL */(E(_1cZ/* stU0 */), toJSStr/* EXTERNAL */(E(_1cV/* stTD */)), _1cY/* stTP */);
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), _1d0/* stU8 */);});
},
_1d1/* getAttr2 */ = "(function (key, jq) { return jq.attr(key); })",
_1d2/* $wa10 */ = function(_1d3/* stLe */, _1d4/* stLf */, _/* EXTERNAL */){
  var _1d5/* stLp */ = eval/* EXTERNAL */(E(_1d1/* FormEngine.JQuery.getAttr2 */)),
  _1d6/* stLx */ = __app2/* EXTERNAL */(E(_1d5/* stLp */), toJSStr/* EXTERNAL */(E(_1d3/* stLe */)), _1d4/* stLf */);
  return new T(function(){
    return String/* EXTERNAL */(_1d6/* stLx */);
  });
},
_1d7/* $wa23 */ = function(_1d8/* stHa */, _1d9/* stHb */, _/* EXTERNAL */){
  var _1da/* stHg */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _1d9/* stHb */),
  _1db/* stHm */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _1da/* stHg */),
  _1dc/* stHq */ = B(_IE/* FormEngine.JQuery.onClick1 */(_1d8/* stHa */, _1db/* stHm */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1dc/* stHq */));});
},
_1dd/* onMouseEnter2 */ = "(function (ev, jq) { jq.mouseenter(ev); })",
_1de/* onMouseEnter1 */ = function(_1df/* stwy */, _1dg/* stwz */, _/* EXTERNAL */){
  var _1dh/* stwL */ = __createJSFunc/* EXTERNAL */(2, function(_1di/* stwC */, _/* EXTERNAL */){
    var _1dj/* stwE */ = B(A2(E(_1df/* stwy */),_1di/* stwC */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1dk/* stwO */ = E(_1dg/* stwz */),
  _1dl/* stwT */ = eval/* EXTERNAL */(E(_1dd/* FormEngine.JQuery.onMouseEnter2 */)),
  _1dm/* stx1 */ = __app2/* EXTERNAL */(E(_1dl/* stwT */), _1dh/* stwL */, _1dk/* stwO */);
  return _1dk/* stwO */;
},
_1dn/* $wa30 */ = function(_1do/* stHH */, _1dp/* stHI */, _/* EXTERNAL */){
  var _1dq/* stHN */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _1dp/* stHI */),
  _1dr/* stHT */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _1dq/* stHN */),
  _1ds/* stHX */ = B(_1de/* FormEngine.JQuery.onMouseEnter1 */(_1do/* stHH */, _1dr/* stHT */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1ds/* stHX */));});
},
_1dt/* onMouseLeave2 */ = "(function (ev, jq) { jq.mouseleave(ev); })",
_1du/* onMouseLeave1 */ = function(_1dv/* stvZ */, _1dw/* stw0 */, _/* EXTERNAL */){
  var _1dx/* stwc */ = __createJSFunc/* EXTERNAL */(2, function(_1dy/* stw3 */, _/* EXTERNAL */){
    var _1dz/* stw5 */ = B(A2(E(_1dv/* stvZ */),_1dy/* stw3 */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1dA/* stwf */ = E(_1dw/* stw0 */),
  _1dB/* stwk */ = eval/* EXTERNAL */(E(_1dt/* FormEngine.JQuery.onMouseLeave2 */)),
  _1dC/* stws */ = __app2/* EXTERNAL */(E(_1dB/* stwk */), _1dx/* stwc */, _1dA/* stwf */);
  return _1dA/* stwf */;
},
_1dD/* $wa31 */ = function(_1dE/* stIe */, _1dF/* stIf */, _/* EXTERNAL */){
  var _1dG/* stIk */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _1dF/* stIf */),
  _1dH/* stIq */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _1dG/* stIk */),
  _1dI/* stIu */ = B(_1du/* FormEngine.JQuery.onMouseLeave1 */(_1dE/* stIe */, _1dH/* stIq */, _/* EXTERNAL */));
  return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1dI/* stIu */));});
},
_1dJ/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span class=\'short-desc\'>"));
}),
_1dK/* setTextInside1 */ = function(_1dL/* stZI */, _1dM/* stZJ */, _/* EXTERNAL */){
  return new F(function(){return _Il/* FormEngine.JQuery.$wa34 */(_1dL/* stZI */, E(_1dM/* stZJ */), _/* EXTERNAL */);});
},
_1dN/* a1 */ = function(_1dO/* sfSD */, _1dP/* sfSE */, _/* EXTERNAL */){
  var _1dQ/* sfSR */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1dO/* sfSD */)))).e);
  if(!_1dQ/* sfSR */._){
    return _1dP/* sfSE */;
  }else{
    var _1dR/* sfSV */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dJ/* FormEngine.FormElement.Rendering.lvl3 */, E(_1dP/* sfSE */), _/* EXTERNAL */));
    return new F(function(){return _1dK/* FormEngine.JQuery.setTextInside1 */(_1dQ/* sfSR */.a, _1dR/* sfSV */, _/* EXTERNAL */);});
  }
},
_1dS/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label>"));
}),
_1dT/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label class=\"link\" onclick=\""));
}),
_1dU/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\">"));
}),
_1dV/* a3 */ = function(_1dW/* sfTe */, _1dX/* sfTf */, _/* EXTERNAL */){
  var _1dY/* sfTi */ = B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1dW/* sfTe */)))),
  _1dZ/* sfTs */ = E(_1dY/* sfTi */.a);
  if(!_1dZ/* sfTs */._){
    return _1dX/* sfTf */;
  }else{
    var _1e0/* sfTt */ = _1dZ/* sfTs */.a,
    _1e1/* sfTu */ = E(_1dY/* sfTi */.g);
    if(!_1e1/* sfTu */._){
      var _1e2/* sfTx */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, E(_1dX/* sfTf */), _/* EXTERNAL */));
      return new F(function(){return _1dK/* FormEngine.JQuery.setTextInside1 */(_1e0/* sfTt */, _1e2/* sfTx */, _/* EXTERNAL */);});
    }else{
      var _1e3/* sfTF */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_1dT/* FormEngine.FormElement.Rendering.lvl7 */, new T(function(){
        return B(_12/* GHC.Base.++ */(_1e1/* sfTu */.a, _1dU/* FormEngine.FormElement.Rendering.lvl8 */));
      },1))), E(_1dX/* sfTf */), _/* EXTERNAL */));
      return new F(function(){return _1dK/* FormEngine.JQuery.setTextInside1 */(_1e0/* sfTt */, _1e3/* sfTF */, _/* EXTERNAL */);});
    }
  }
},
_1e4/* a4 */ = function(_1e5/* sfUm */, _/* EXTERNAL */){
  var _1e6/* sfUs */ = B(_56/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_1e5/* sfUm */)))), _LE/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */));
  }))), _/* EXTERNAL */)),
  _1e7/* sfUx */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, E(_1e6/* sfUs */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1e8/* findSelector2 */ = "(function (elJs, jq) { return jq.find(elJs); })",
_1e9/* $wa9 */ = function(_1ea/* stZQ */, _1eb/* stZR */, _/* EXTERNAL */){
  var _1ec/* su01 */ = eval/* EXTERNAL */(E(_1e8/* FormEngine.JQuery.findSelector2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_1ec/* su01 */), toJSStr/* EXTERNAL */(E(_1ea/* stZQ */)), _1eb/* stZR */);});
},
_1ed/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("span"));
}),
_1ee/* a5 */ = function(_1ef/* sfUA */, _/* EXTERNAL */){
  var _1eg/* sfUG */ = B(_56/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_1ef/* sfUA */)))), _LE/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */));
  }))), _/* EXTERNAL */)),
  _1eh/* sfUJ */ = E(_1eg/* sfUG */),
  _1ei/* sfUL */ = B(_1e9/* FormEngine.JQuery.$wa9 */(_1ed/* FormEngine.FormElement.Rendering.lvl9 */, _1eh/* sfUJ */, _/* EXTERNAL */)),
  _1ej/* sfUZ */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1ef/* sfUA */)))).f);
  if(!_1ej/* sfUZ */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _1ek/* sfV3 */ = B(_L2/* FormEngine.JQuery.$wa26 */(_1ej/* sfUZ */.a, E(_1ei/* sfUL */), _/* EXTERNAL */)),
    _1el/* sfV6 */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _IW/* FormEngine.JQuery.appearJq2 */, _1eh/* sfUJ */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_1em/* flagPlaceId */ = function(_1en/* sc7M */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1en/* sc7M */)), _1aC/* FormEngine.FormElement.Identifiers.flagPlaceId1 */);});
},
_1eo/* funcImg */ = function(_1ep/* sa6d */){
  return E(E(_1ep/* sa6d */).a);
},
_1eq/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table>"));
}),
_1er/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tbody>"));
}),
_1es/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tr>"));
}),
_1et/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td>"));
}),
_1eu/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("more-space"));
}),
_1ev/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd\'>"));
}),
_1ew/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1ex/* $wa2 */ = function(_1ey/* sfV9 */, _1ez/* sfVa */, _1eA/* sfVb */, _1eB/* sfVc */, _1eC/* sfVd */, _/* EXTERNAL */){
  var _1eD/* sfVf */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1eq/* FormEngine.FormElement.Rendering.lvl10 */, _1eC/* sfVd */, _/* EXTERNAL */)),
  _1eE/* sfVn */ = B(_1dn/* FormEngine.JQuery.$wa30 */(function(_1eF/* sfVk */, _/* EXTERNAL */){
    return new F(function(){return _1ee/* FormEngine.FormElement.Rendering.a5 */(_1ez/* sfVa */, _/* EXTERNAL */);});
  }, E(_1eD/* sfVf */), _/* EXTERNAL */)),
  _1eG/* sfVv */ = B(_1dD/* FormEngine.JQuery.$wa31 */(function(_1eH/* sfVs */, _/* EXTERNAL */){
    return new F(function(){return _1e4/* FormEngine.FormElement.Rendering.a4 */(_1ez/* sfVa */, _/* EXTERNAL */);});
  }, E(_1eE/* sfVn */), _/* EXTERNAL */)),
  _1eI/* sfVA */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
  _1eJ/* sfVD */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1eG/* sfVv */)),
  _1eK/* sfVG */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
  _1eL/* sfVJ */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1eJ/* sfVD */),
  _1eM/* sfVM */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1er/* FormEngine.FormElement.Rendering.lvl11 */, _1eL/* sfVJ */, _/* EXTERNAL */)),
  _1eN/* sfVS */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1eM/* sfVM */)),
  _1eO/* sfVW */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1eN/* sfVS */),
  _1eP/* sfVZ */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1es/* FormEngine.FormElement.Rendering.lvl12 */, _1eO/* sfVW */, _/* EXTERNAL */)),
  _1eQ/* sfW5 */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1eP/* sfVZ */)),
  _1eR/* sfW9 */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1eQ/* sfW5 */),
  _1eS/* sfWg */ = function(_/* EXTERNAL */, _1eT/* sfWi */){
    var _1eU/* sfWj */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1ev/* FormEngine.FormElement.Rendering.lvl15 */, _1eT/* sfWi */, _/* EXTERNAL */)),
    _1eV/* sfWp */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1eU/* sfWj */)),
    _1eW/* sfWt */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1eV/* sfWp */),
    _1eX/* sfWw */ = B(_HO/* FormEngine.JQuery.$wa */(_1eu/* FormEngine.FormElement.Rendering.lvl14 */, _1eW/* sfWt */, _/* EXTERNAL */)),
    _1eY/* sfWz */ = B(_1dV/* FormEngine.FormElement.Rendering.a3 */(_1ez/* sfVa */, _1eX/* sfWw */, _/* EXTERNAL */)),
    _1eZ/* sfWE */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
    _1f0/* sfWH */ = __app1/* EXTERNAL */(_1eZ/* sfWE */, E(_1eY/* sfWz */)),
    _1f1/* sfWK */ = B(A1(_1ey/* sfV9 */,_/* EXTERNAL */)),
    _1f2/* sfWN */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1et/* FormEngine.FormElement.Rendering.lvl13 */, _1f0/* sfWH */, _/* EXTERNAL */)),
    _1f3/* sfWT */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1f2/* sfWN */)),
    _1f4/* sfWX */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1f3/* sfWT */),
    _1f5/* sfX5 */ = __app2/* EXTERNAL */(E(_Is/* FormEngine.JQuery.appendJq_f1 */), E(_1f1/* sfWK */), _1f4/* sfWX */),
    _1f6/* sfX9 */ = __app1/* EXTERNAL */(_1eZ/* sfWE */, _1f5/* sfX5 */),
    _1f7/* sfXc */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1et/* FormEngine.FormElement.Rendering.lvl13 */, _1f6/* sfX9 */, _/* EXTERNAL */)),
    _1f8/* sfXi */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, new T(function(){
      return B(_1em/* FormEngine.FormElement.Identifiers.flagPlaceId */(_1ez/* sfVa */));
    },1), E(_1f7/* sfXc */), _/* EXTERNAL */)),
    _1f9/* sfXo */ = __app1/* EXTERNAL */(_1eZ/* sfWE */, E(_1f8/* sfXi */)),
    _1fa/* sfXs */ = __app1/* EXTERNAL */(_1eZ/* sfWE */, _1f9/* sfXo */),
    _1fb/* sfXw */ = __app1/* EXTERNAL */(_1eZ/* sfWE */, _1fa/* sfXs */);
    return new F(function(){return _1dN/* FormEngine.FormElement.Rendering.a1 */(_1ez/* sfVa */, _1fb/* sfXw */, _/* EXTERNAL */);});
  },
  _1fc/* sfXA */ = E(E(_1eB/* sfVc */).c);
  if(!_1fc/* sfXA */._){
    return new F(function(){return _1eS/* sfWg */(_/* EXTERNAL */, _1eR/* sfW9 */);});
  }else{
    var _1fd/* sfXB */ = _1fc/* sfXA */.a,
    _1fe/* sfXC */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1et/* FormEngine.FormElement.Rendering.lvl13 */, _1eR/* sfW9 */, _/* EXTERNAL */)),
    _1ff/* sfXI */ = __app1/* EXTERNAL */(_1eI/* sfVA */, E(_1fe/* sfXC */)),
    _1fg/* sfXM */ = __app1/* EXTERNAL */(_1eK/* sfVG */, _1ff/* sfXI */),
    _1fh/* sfXP */ = B(_HO/* FormEngine.JQuery.$wa */(_1eu/* FormEngine.FormElement.Rendering.lvl14 */, _1fg/* sfXM */, _/* EXTERNAL */)),
    _1fi/* sfXV */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_1eo/* FormEngine.Functionality.funcImg */(_1fd/* sfXB */)), E(_1fh/* sfXP */), _/* EXTERNAL */)),
    _1fj/* sfY0 */ = new T(function(){
      return B(A2(E(_1fd/* sfXB */).b,_1ez/* sfVa */, _1eA/* sfVb */));
    }),
    _1fk/* sfY6 */ = B(_1d7/* FormEngine.JQuery.$wa23 */(function(_1fl/* sfY4 */){
      return E(_1fj/* sfY0 */);
    }, E(_1fi/* sfXV */), _/* EXTERNAL */)),
    _1fm/* sfYe */ = __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1fk/* sfY6 */));
    return new F(function(){return _1eS/* sfWg */(_/* EXTERNAL */, _1fm/* sfYe */);});
  }
},
_1fn/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h"));
}),
_1fo/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(">"));
}),
_1fp/* a2 */ = function(_1fq/* sfSY */, _1fr/* sfSZ */, _1fs/* sfT0 */, _/* EXTERNAL */){
  var _1ft/* sfT2 */ = E(_1fq/* sfSY */);
  if(!_1ft/* sfT2 */._){
    return _1fs/* sfT0 */;
  }else{
    var _1fu/* sfTb */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_1fn/* FormEngine.FormElement.Rendering.lvl4 */, new T(function(){
      return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1fr/* sfSZ */), _I/* GHC.Types.[] */)), _1fo/* FormEngine.FormElement.Rendering.lvl5 */));
    },1))), E(_1fs/* sfT0 */), _/* EXTERNAL */));
    return new F(function(){return _1dK/* FormEngine.JQuery.setTextInside1 */(_1ft/* sfT2 */.a, _1fu/* sfTb */, _/* EXTERNAL */);});
  }
},
_1fv/* target_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (js) {return $(js.target); })");
}),
_1fw/* $wa3 */ = function(_1fx/* sfYh */, _/* EXTERNAL */){
  var _1fy/* sfYm */ = __app1/* EXTERNAL */(E(_1fv/* FormEngine.JQuery.target_f1 */), _1fx/* sfYh */),
  _1fz/* sfYp */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
  _1fA/* sfYs */ = __app1/* EXTERNAL */(_1fz/* sfYp */, _1fy/* sfYm */),
  _1fB/* sfYw */ = __app1/* EXTERNAL */(_1fz/* sfYp */, _1fA/* sfYs */),
  _1fC/* sfYA */ = __app1/* EXTERNAL */(_1fz/* sfYp */, _1fB/* sfYw */),
  _1fD/* sfYE */ = __app1/* EXTERNAL */(_1fz/* sfYp */, _1fC/* sfYA */),
  _1fE/* sfYK */ = __app1/* EXTERNAL */(E(_1aH/* FormEngine.JQuery.removeJq_f1 */), _1fD/* sfYE */);
  return _0/* GHC.Tuple.() */;
},
_1fF/* a6 */ = function(_1fG/* sfYN */, _/* EXTERNAL */){
  return new F(function(){return _1fw/* FormEngine.FormElement.Rendering.$wa3 */(E(_1fG/* sfYN */), _/* EXTERNAL */);});
},
_1fH/* a7 */ = function(_1fI/* sfYW */, _/* EXTERNAL */){
  while(1){
    var _1fJ/* sfYY */ = E(_1fI/* sfYW */);
    if(!_1fJ/* sfYY */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _1fK/* sfZ3 */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, E(_1fJ/* sfYY */.a), _/* EXTERNAL */));
      _1fI/* sfYW */ = _1fJ/* sfYY */.b;
      continue;
    }
  }
},
_1fL/* addImg */ = function(_1fM/* s9ZX */){
  return E(E(_1fM/* s9ZX */).d);
},
_1fN/* appendT1 */ = function(_1fO/* stSy */, _1fP/* stSz */, _/* EXTERNAL */){
  return new F(function(){return _Ig/* FormEngine.JQuery.$wa3 */(_1fO/* stSy */, E(_1fP/* stSz */), _/* EXTERNAL */);});
},
_1fQ/* checkboxId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_optional_group"));
}),
_1fR/* errorjq1 */ = function(_1fS/* stBR */, _1fT/* stBS */, _/* EXTERNAL */){
  var _1fU/* stC2 */ = eval/* EXTERNAL */(E(_5P/* FormEngine.JQuery.errorIO2 */)),
  _1fV/* stCa */ = __app1/* EXTERNAL */(E(_1fU/* stC2 */), toJSStr/* EXTERNAL */(E(_1fS/* stBR */)));
  return _1fT/* stBS */;
},
_1fW/* go */ = function(_1fX/* sfYR */, _1fY/* sfYS */){
  while(1){
    var _1fZ/* sfYT */ = E(_1fX/* sfYR */);
    if(!_1fZ/* sfYT */._){
      return E(_1fY/* sfYS */);
    }else{
      _1fX/* sfYR */ = _1fZ/* sfYT */.b;
      _1fY/* sfYS */ = _1fZ/* sfYT */.a;
      continue;
    }
  }
},
_1g0/* ifiText1 */ = new T(function(){
  return B(_19R/* Control.Exception.Base.recSelError */("ifiText"));
}),
_1g1/* isChecked_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.prop(\'checked\') === true; })");
}),
_1g2/* isRadioSelected_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.length; })");
}),
_1g3/* isRadioSelected1 */ = function(_1g4/* stOD */, _/* EXTERNAL */){
  var _1g5/* stOO */ = eval/* EXTERNAL */(E(_Pg/* FormEngine.JQuery.getRadioValue2 */)),
  _1g6/* stOW */ = __app1/* EXTERNAL */(E(_1g5/* stOO */), toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Pi/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1g4/* stOD */, _Ph/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _1g7/* stP2 */ = __app1/* EXTERNAL */(E(_1g2/* FormEngine.JQuery.isRadioSelected_f1 */), _1g6/* stOW */);
  return new T(function(){
    var _1g8/* stP6 */ = Number/* EXTERNAL */(_1g7/* stP2 */),
    _1g9/* stPa */ = jsTrunc/* EXTERNAL */(_1g8/* stP6 */);
    return _1g9/* stPa */>0;
  });
},
_1ga/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_1gb/* errorEmptyList */ = function(_1gc/* s9sr */){
  return new F(function(){return err/* EXTERNAL */(B(_12/* GHC.Base.++ */(_6Q/* GHC.List.prel_list_str */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1gc/* s9sr */, _1ga/* GHC.List.lvl */));
  },1))));});
},
_1gd/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_1ge/* last1 */ = new T(function(){
  return B(_1gb/* GHC.List.errorEmptyList */(_1gd/* GHC.List.lvl16 */));
}),
_1gf/* lfiAvailableOptions1 */ = new T(function(){
  return B(_19R/* Control.Exception.Base.recSelError */("lfiAvailableOptions"));
}),
_1gg/* readEither4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: no parse"));
}),
_1gh/* lvl */ = new T(function(){
  return B(err/* EXTERNAL */(_1gg/* Text.Read.readEither4 */));
}),
_1gi/* readEither2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude.read: ambiguous parse"));
}),
_1gj/* lvl1 */ = new T(function(){
  return B(err/* EXTERNAL */(_1gi/* Text.Read.readEither2 */));
}),
_1gk/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Submit"));
}),
_1gl/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("value"));
}),
_1gm/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'button\' class=\'submit\'>"));
}),
_1gn/* $fReadInt3 */ = function(_1go/* s1vlT */, _1gp/* s1vlU */){
  var _1gq/* s1vmt */ = function(_1gr/* s1vlV */, _1gs/* s1vlW */){
    var _1gt/* s1vlX */ = function(_1gu/* s1vlY */){
      return new F(function(){return A1(_1gs/* s1vlW */,new T(function(){
        return  -E(_1gu/* s1vlY */);
      }));});
    },
    _1gv/* s1vm5 */ = new T(function(){
      return B(_128/* Text.Read.Lex.expect2 */(function(_1gw/* s1vm4 */){
        return new F(function(){return A3(_1go/* s1vlT */,_1gw/* s1vm4 */, _1gr/* s1vlV */, _1gt/* s1vlX */);});
      }));
    }),
    _1gx/* s1vm6 */ = function(_1gy/* s1vm7 */){
      return E(_1gv/* s1vm5 */);
    },
    _1gz/* s1vm8 */ = function(_1gA/* s1vm9 */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1gA/* s1vm9 */, _1gx/* s1vm6 */);});
    },
    _1gB/* s1vmo */ = new T(function(){
      return B(_128/* Text.Read.Lex.expect2 */(function(_1gC/* s1vmc */){
        var _1gD/* s1vmd */ = E(_1gC/* s1vmc */);
        if(_1gD/* s1vmd */._==4){
          var _1gE/* s1vmf */ = E(_1gD/* s1vmd */.a);
          if(!_1gE/* s1vmf */._){
            return new F(function(){return A3(_1go/* s1vlT */,_1gD/* s1vmd */, _1gr/* s1vlV */, _1gs/* s1vlW */);});
          }else{
            if(E(_1gE/* s1vmf */.a)==45){
              if(!E(_1gE/* s1vmf */.b)._){
                return E(new T1(1,_1gz/* s1vm8 */));
              }else{
                return new F(function(){return A3(_1go/* s1vlT */,_1gD/* s1vmd */, _1gr/* s1vlV */, _1gs/* s1vlW */);});
              }
            }else{
              return new F(function(){return A3(_1go/* s1vlT */,_1gD/* s1vmd */, _1gr/* s1vlV */, _1gs/* s1vlW */);});
            }
          }
        }else{
          return new F(function(){return A3(_1go/* s1vlT */,_1gD/* s1vmd */, _1gr/* s1vlV */, _1gs/* s1vlW */);});
        }
      }));
    }),
    _1gF/* s1vmp */ = function(_1gG/* s1vmq */){
      return E(_1gB/* s1vmo */);
    };
    return new T1(1,function(_1gH/* s1vmr */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1gH/* s1vmr */, _1gF/* s1vmp */);});
    });
  };
  return new F(function(){return _12Z/* GHC.Read.$fReadDouble10 */(_1gq/* s1vmt */, _1gp/* s1vlU */);});
},
_1gI/* numberToInteger */ = function(_1gJ/* s1ojv */){
  var _1gK/* s1ojw */ = E(_1gJ/* s1ojv */);
  if(!_1gK/* s1ojw */._){
    var _1gL/* s1ojy */ = _1gK/* s1ojw */.b,
    _1gM/* s1ojF */ = new T(function(){
      return B(_Ul/* Text.Read.Lex.numberToFixed_go */(new T(function(){
        return B(_U1/* GHC.Integer.Type.smallInteger */(E(_1gK/* s1ojw */.a)));
      }), new T(function(){
        return B(_TW/* GHC.List.$wlenAcc */(_1gL/* s1ojy */, 0));
      },1), B(_2S/* GHC.Base.map */(_U3/* Text.Read.Lex.numberToFixed2 */, _1gL/* s1ojy */))));
    });
    return new T1(1,_1gM/* s1ojF */);
  }else{
    return (E(_1gK/* s1ojw */.b)._==0) ? (E(_1gK/* s1ojw */.c)._==0) ? new T1(1,new T(function(){
      return B(_UC/* Text.Read.Lex.valInteger */(_TV/* Text.Read.Lex.numberToFixed1 */, _1gK/* s1ojw */.a));
    })) : __Z/* EXTERNAL */ : __Z/* EXTERNAL */;
  }
},
_1gN/* $fReadInt_$sconvertInt */ = function(_1gO/* s1vie */){
  var _1gP/* s1vif */ = E(_1gO/* s1vie */);
  if(_1gP/* s1vif */._==5){
    var _1gQ/* s1vih */ = B(_1gI/* Text.Read.Lex.numberToInteger */(_1gP/* s1vif */.a));
    if(!_1gQ/* s1vih */._){
      return E(_16L/* Text.ParserCombinators.ReadPrec.pfail1 */);
    }else{
      var _1gR/* s1vij */ = new T(function(){
        return B(_Vw/* GHC.Integer.Type.integerToInt */(_1gQ/* s1vih */.a));
      });
      return function(_1gS/* s1vil */, _1gT/* s1vim */){
        return new F(function(){return A1(_1gT/* s1vim */,_1gR/* s1vij */);});
      };
    }
  }else{
    return E(_16L/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_1gU/* lvl2 */ = new T(function(){
  return B(A3(_1gn/* GHC.Read.$fReadInt3 */,_1gN/* GHC.Read.$fReadInt_$sconvertInt */, _12F/* Text.ParserCombinators.ReadPrec.minPrec */, _18G/* Text.Read.readEither5 */));
}),
_1gV/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd more-space\' style=\'text-align: center\'>"));
}),
_1gW/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table style=\'margin-top: 10px\'>"));
}),
_1gX/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save"));
}),
_1gY/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'submit\'>"));
}),
_1gZ/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("count"));
}),
_1h0/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1"));
}),
_1h1/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("level"));
}),
_1h2/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("framed"));
}),
_1h3/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'multiple-group\'>"));
}),
_1h4/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td style=\'vertical-align: middle;\'>"));
}),
_1h5/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'multiple-section\'>"));
}),
_1h6/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-section\'>"));
}),
_1h7/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u25be"));
}),
_1h8/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1h9/* lvl34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("checked"));
}),
_1ha/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("name"));
}),
_1hb/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'checkbox\'>"));
}),
_1hc/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-group\'>"));
}),
_1hd/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'simple-group\'>"));
}),
_1he/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("selected"));
}),
_1hf/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<option>"));
}),
_1hg/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("identity"));
}),
_1hh/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<select>"));
}),
_1hi/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div>"));
}),
_1hj/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<br>"));
}),
_1hk/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'radio\'>"));
}),
_1hl/* lvl46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div></div>"));
}),
_1hm/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'more-space\' colspan=\'2\'>"));
}),
_1hn/* lvl48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;&nbsp;"));
}),
_1ho/* lvl49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;"));
}),
_1hp/* lvl50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'number\' step=\'any\'>"));
}),
_1hq/* lvl51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'email\'>"));
}),
_1hr/* lvl52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<textarea>"));
}),
_1hs/* lvl53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'text\'>"));
}),
_1ht/* lvl54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("renderElement did not unify"));
}),
_1hu/* lvl55 */ = new T(function(){
  return B(_4e/* GHC.Show.$wshowSignedInt */(0, 0, _I/* GHC.Types.[] */));
}),
_1hv/* onBlur2 */ = "(function (ev, jq) { jq.blur(ev); })",
_1hw/* onBlur1 */ = function(_1hx/* styO */, _1hy/* styP */, _/* EXTERNAL */){
  var _1hz/* stz1 */ = __createJSFunc/* EXTERNAL */(2, function(_1hA/* styS */, _/* EXTERNAL */){
    var _1hB/* styU */ = B(A2(E(_1hx/* styO */),_1hA/* styS */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1hC/* stz4 */ = E(_1hy/* styP */),
  _1hD/* stz9 */ = eval/* EXTERNAL */(E(_1hv/* FormEngine.JQuery.onBlur2 */)),
  _1hE/* stzh */ = __app2/* EXTERNAL */(E(_1hD/* stz9 */), _1hz/* stz1 */, _1hC/* stz4 */);
  return _1hC/* stz4 */;
},
_1hF/* onChange2 */ = "(function (ev, jq) { jq.change(ev); })",
_1hG/* onChange1 */ = function(_1hH/* stx7 */, _1hI/* stx8 */, _/* EXTERNAL */){
  var _1hJ/* stxk */ = __createJSFunc/* EXTERNAL */(2, function(_1hK/* stxb */, _/* EXTERNAL */){
    var _1hL/* stxd */ = B(A2(E(_1hH/* stx7 */),_1hK/* stxb */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1hM/* stxn */ = E(_1hI/* stx8 */),
  _1hN/* stxs */ = eval/* EXTERNAL */(E(_1hF/* FormEngine.JQuery.onChange2 */)),
  _1hO/* stxA */ = __app2/* EXTERNAL */(E(_1hN/* stxs */), _1hJ/* stxk */, _1hM/* stxn */);
  return _1hM/* stxn */;
},
_1hP/* onKeyup2 */ = "(function (ev, jq) { jq.keyup(ev); })",
_1hQ/* onKeyup1 */ = function(_1hR/* styf */, _1hS/* styg */, _/* EXTERNAL */){
  var _1hT/* stys */ = __createJSFunc/* EXTERNAL */(2, function(_1hU/* styj */, _/* EXTERNAL */){
    var _1hV/* styl */ = B(A2(E(_1hR/* styf */),_1hU/* styj */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1hW/* styv */ = E(_1hS/* styg */),
  _1hX/* styA */ = eval/* EXTERNAL */(E(_1hP/* FormEngine.JQuery.onKeyup2 */)),
  _1hY/* styI */ = __app2/* EXTERNAL */(E(_1hX/* styA */), _1hT/* stys */, _1hW/* styv */);
  return _1hW/* styv */;
},
_1hZ/* optionElemValue */ = function(_1i0/* s6MQ */){
  var _1i1/* s6MR */ = E(_1i0/* s6MQ */);
  if(!_1i1/* s6MR */._){
    var _1i2/* s6MU */ = E(_1i1/* s6MR */.a);
    return (_1i2/* s6MU */._==0) ? E(_1i2/* s6MU */.a) : E(_1i2/* s6MU */.b);
  }else{
    var _1i3/* s6N2 */ = E(_1i1/* s6MR */.a);
    return (_1i3/* s6N2 */._==0) ? E(_1i3/* s6N2 */.a) : E(_1i3/* s6N2 */.b);
  }
},
_1i4/* optionSectionId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_detail"));
}),
_1i5/* prev_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.prev(); })");
}),
_1i6/* filter */ = function(_1i7/*  s9DD */, _1i8/*  s9DE */){
  while(1){
    var _1i9/*  filter */ = B((function(_1ia/* s9DD */, _1ib/* s9DE */){
      var _1ic/* s9DF */ = E(_1ib/* s9DE */);
      if(!_1ic/* s9DF */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1id/* s9DG */ = _1ic/* s9DF */.a,
        _1ie/* s9DH */ = _1ic/* s9DF */.b;
        if(!B(A1(_1ia/* s9DD */,_1id/* s9DG */))){
          var _1if/*   s9DD */ = _1ia/* s9DD */;
          _1i7/*  s9DD */ = _1if/*   s9DD */;
          _1i8/*  s9DE */ = _1ie/* s9DH */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1id/* s9DG */,new T(function(){
            return B(_1i6/* GHC.List.filter */(_1ia/* s9DD */, _1ie/* s9DH */));
          }));
        }
      }
    })(_1i7/*  s9DD */, _1i8/*  s9DE */));
    if(_1i9/*  filter */!=__continue/* EXTERNAL */){
      return _1i9/*  filter */;
    }
  }
},
_1ig/* $wlvl */ = function(_1ih/* sc72 */){
  var _1ii/* sc73 */ = function(_1ij/* sc74 */){
    var _1ik/* sc75 */ = function(_1il/* sc76 */){
      if(_1ih/* sc72 */<48){
        switch(E(_1ih/* sc72 */)){
          case 45:
            return true;
          case 95:
            return true;
          default:
            return false;
        }
      }else{
        if(_1ih/* sc72 */>57){
          switch(E(_1ih/* sc72 */)){
            case 45:
              return true;
            case 95:
              return true;
            default:
              return false;
          }
        }else{
          return true;
        }
      }
    };
    if(_1ih/* sc72 */<97){
      return new F(function(){return _1ik/* sc75 */(_/* EXTERNAL */);});
    }else{
      if(_1ih/* sc72 */>122){
        return new F(function(){return _1ik/* sc75 */(_/* EXTERNAL */);});
      }else{
        return true;
      }
    }
  };
  if(_1ih/* sc72 */<65){
    return new F(function(){return _1ii/* sc73 */(_/* EXTERNAL */);});
  }else{
    if(_1ih/* sc72 */>90){
      return new F(function(){return _1ii/* sc73 */(_/* EXTERNAL */);});
    }else{
      return true;
    }
  }
},
_1im/* radioId1 */ = function(_1in/* sc7l */){
  return new F(function(){return _1ig/* FormEngine.FormElement.Identifiers.$wlvl */(E(_1in/* sc7l */));});
},
_1io/* radioId2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_1ip/* radioId */ = function(_1iq/* sc7o */, _1ir/* sc7p */){
  var _1is/* sc7I */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_1io/* FormEngine.FormElement.Identifiers.radioId2 */, new T(function(){
      var _1it/* sc7r */ = E(_1ir/* sc7p */);
      if(!_1it/* sc7r */._){
        var _1iu/* sc7u */ = E(_1it/* sc7r */.a);
        if(!_1iu/* sc7u */._){
          return B(_1i6/* GHC.List.filter */(_1im/* FormEngine.FormElement.Identifiers.radioId1 */, _1iu/* sc7u */.a));
        }else{
          return B(_1i6/* GHC.List.filter */(_1im/* FormEngine.FormElement.Identifiers.radioId1 */, _1iu/* sc7u */.b));
        }
      }else{
        var _1iv/* sc7C */ = E(_1it/* sc7r */.a);
        if(!_1iv/* sc7C */._){
          return B(_1i6/* GHC.List.filter */(_1im/* FormEngine.FormElement.Identifiers.radioId1 */, _1iv/* sc7C */.a));
        }else{
          return B(_1i6/* GHC.List.filter */(_1im/* FormEngine.FormElement.Identifiers.radioId1 */, _1iv/* sc7C */.b));
        }
      }
    },1)));
  },1);
  return new F(function(){return _12/* GHC.Base.++ */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1iq/* sc7o */)), _1is/* sc7I */);});
},
_1iw/* setGroupInGroup */ = function(_1ix/* s6Yg */, _1iy/* s6Yh */){
  var _1iz/* s6Yi */ = E(_1iy/* s6Yh */),
  _1iA/* s6Ym */ = new T(function(){
    return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
      return new F(function(){return _1iC/* FormEngine.FormElement.FormElement.setGroupOfElem */(_1ix/* s6Yg */, _1iB/* B1 */);});
    }, _1iz/* s6Yi */.a));
  });
  return new T2(0,_1iA/* s6Ym */,_1iz/* s6Yi */.b);
},
_1iD/* setGroupInOption */ = function(_1iE/* s6Yn */, _1iF/* s6Yo */){
  var _1iG/* s6Yp */ = E(_1iF/* s6Yo */);
  if(!_1iG/* s6Yp */._){
    return E(_1iG/* s6Yp */);
  }else{
    var _1iH/* s6Yw */ = new T(function(){
      return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
        return new F(function(){return _1iC/* FormEngine.FormElement.FormElement.setGroupOfElem */(_1iE/* s6Yn */, _1iB/* B1 */);});
      }, _1iG/* s6Yp */.c));
    });
    return new T3(1,_1iG/* s6Yp */.a,_1iG/* s6Yp */.b,_1iH/* s6Yw */);
  }
},
_1iC/* setGroupOfElem */ = function(_1iI/* s6Yx */, _1iJ/* s6Yy */){
  var _1iK/* s6Yz */ = E(_1iJ/* s6Yy */);
  switch(_1iK/* s6Yz */._){
    case 1:
      var _1iL/* s6YK */ = new T(function(){
        var _1iM/* s6YE */ = E(_1iI/* s6Yx */);
        if(!_1iM/* s6YE */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iM/* s6YE */.a).b);
          }));
        }
      });
      return new T4(1,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1iL/* s6YK */,_1iK/* s6Yz */.d);
    case 2:
      var _1iN/* s6YV */ = new T(function(){
        var _1iO/* s6YP */ = E(_1iI/* s6Yx */);
        if(!_1iO/* s6YP */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iO/* s6YP */.a).b);
          }));
        }
      });
      return new T4(2,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1iN/* s6YV */,_1iK/* s6Yz */.d);
    case 3:
      var _1iP/* s6Z6 */ = new T(function(){
        var _1iQ/* s6Z0 */ = E(_1iI/* s6Yx */);
        if(!_1iQ/* s6Z0 */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iQ/* s6Z0 */.a).b);
          }));
        }
      });
      return new T4(3,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1iP/* s6Z6 */,_1iK/* s6Yz */.d);
    case 4:
      var _1iR/* s6Zi */ = new T(function(){
        var _1iS/* s6Zc */ = E(_1iI/* s6Yx */);
        if(!_1iS/* s6Zc */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iS/* s6Zc */.a).b);
          }));
        }
      });
      return new T5(4,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1iK/* s6Yz */.c,_1iR/* s6Zi */,_1iK/* s6Yz */.e);
    case 6:
      var _1iT/* s6Zv */ = new T(function(){
        var _1iU/* s6Zp */ = E(_1iI/* s6Yx */);
        if(!_1iU/* s6Zp */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iU/* s6Zp */.a).b);
          }));
        }
      }),
      _1iV/* s6Zo */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
          return new F(function(){return _1iD/* FormEngine.FormElement.FormElement.setGroupInOption */(_1iI/* s6Yx */, _1iB/* B1 */);});
        }, _1iK/* s6Yz */.b));
      });
      return new T4(6,_1iK/* s6Yz */.a,_1iV/* s6Zo */,_1iT/* s6Zv */,_1iK/* s6Yz */.d);
    case 7:
      var _1iW/* s6ZG */ = new T(function(){
        var _1iX/* s6ZA */ = E(_1iI/* s6Yx */);
        if(!_1iX/* s6ZA */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iX/* s6ZA */.a).b);
          }));
        }
      });
      return new T4(7,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1iW/* s6ZG */,_1iK/* s6Yz */.d);
    case 8:
      var _1iY/* s6ZT */ = new T(function(){
        var _1iZ/* s6ZN */ = E(_1iI/* s6Yx */);
        if(!_1iZ/* s6ZN */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1iZ/* s6ZN */.a).b);
          }));
        }
      }),
      _1j0/* s6ZM */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
          return new F(function(){return _1iC/* FormEngine.FormElement.FormElement.setGroupOfElem */(_1iI/* s6Yx */, _1iB/* B1 */);});
        }, _1iK/* s6Yz */.b));
      });
      return new T4(8,_1iK/* s6Yz */.a,_1j0/* s6ZM */,_1iY/* s6ZT */,_1iK/* s6Yz */.d);
    case 9:
      var _1j1/* s707 */ = new T(function(){
        var _1j2/* s701 */ = E(_1iI/* s6Yx */);
        if(!_1j2/* s701 */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1j2/* s701 */.a).b);
          }));
        }
      }),
      _1j3/* s700 */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
          return new F(function(){return _1iC/* FormEngine.FormElement.FormElement.setGroupOfElem */(_1iI/* s6Yx */, _1iB/* B1 */);});
        }, _1iK/* s6Yz */.c));
      });
      return new T5(9,_1iK/* s6Yz */.a,_1iK/* s6Yz */.b,_1j3/* s700 */,_1j1/* s707 */,_1iK/* s6Yz */.e);
    case 10:
      var _1j4/* s70k */ = new T(function(){
        var _1j5/* s70e */ = E(_1iI/* s6Yx */);
        if(!_1j5/* s70e */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1j5/* s70e */.a).b);
          }));
        }
      }),
      _1j6/* s70d */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_1iB/* B1 */){
          return new F(function(){return _1iw/* FormEngine.FormElement.FormElement.setGroupInGroup */(_1iI/* s6Yx */, _1iB/* B1 */);});
        }, _1iK/* s6Yz */.b));
      });
      return new T4(10,_1iK/* s6Yz */.a,_1j6/* s70d */,_1j4/* s70k */,_1iK/* s6Yz */.d);
    default:
      return E(_1iK/* s6Yz */);
  }
},
_1j7/* foldElements2 */ = function(_1j8/* sfZ6 */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1jb/* sfZ9 */, _/* EXTERNAL */){
  var _1jc/* sfZb */ = function(_1jd/* sfZc */, _/* EXTERNAL */){
    return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1j8/* sfZ6 */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
  },
  _1je/* sfZe */ = new T(function(){
    return B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1j8/* sfZ6 */));
  }),
  _1jf/* sfZf */ = E(_1j8/* sfZ6 */);
  switch(_1jf/* sfZf */._){
    case 0:
      return new F(function(){return _1fR/* FormEngine.JQuery.errorjq1 */(_1ht/* FormEngine.FormElement.Rendering.lvl54 */, _1jb/* sfZ9 */, _/* EXTERNAL */);});
      break;
    case 1:
      var _1jg/* sg0p */ = function(_/* EXTERNAL */){
        var _1jh/* sfZq */ = B(_56/* FormEngine.JQuery.select1 */(_1hs/* FormEngine.FormElement.Rendering.lvl53 */, _/* EXTERNAL */)),
        _1ji/* sfZv */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1jh/* sfZq */), _/* EXTERNAL */)),
        _1jj/* sfZI */ = function(_/* EXTERNAL */, _1jk/* sfZK */){
          var _1jl/* sfZL */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1jf/* sfZf */.b, _1jk/* sfZK */, _/* EXTERNAL */)),
          _1jm/* sfZR */ = B(_1de/* FormEngine.JQuery.onMouseEnter1 */(function(_1jn/* sfZO */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jl/* sfZL */, _/* EXTERNAL */)),
          _1jo/* sfZX */ = B(_1hQ/* FormEngine.JQuery.onKeyup1 */(function(_1jp/* sfZU */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jm/* sfZR */, _/* EXTERNAL */)),
          _1jq/* sg03 */ = B(_1hw/* FormEngine.JQuery.onBlur1 */(function(_1jr/* sg00 */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jo/* sfZX */, _/* EXTERNAL */));
          return new F(function(){return _1du/* FormEngine.JQuery.onMouseLeave1 */(function(_1js/* sg06 */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jq/* sg03 */, _/* EXTERNAL */);});
        },
        _1jt/* sg09 */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).c);
        if(!_1jt/* sg09 */._){
          var _1ju/* sg0c */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _I/* GHC.Types.[] */, E(_1ji/* sfZv */), _/* EXTERNAL */));
          return new F(function(){return _1jj/* sfZI */(_/* EXTERNAL */, E(_1ju/* sg0c */));});
        }else{
          var _1jv/* sg0k */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1jt/* sg09 */.a, E(_1ji/* sfZv */), _/* EXTERNAL */));
          return new F(function(){return _1jj/* sfZI */(_/* EXTERNAL */, E(_1jv/* sg0k */));});
        }
      };
      return new F(function(){return _1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1jg/* sg0p */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */);});
      break;
    case 2:
      var _1jw/* sg1w */ = function(_/* EXTERNAL */){
        var _1jx/* sg0x */ = B(_56/* FormEngine.JQuery.select1 */(_1hr/* FormEngine.FormElement.Rendering.lvl52 */, _/* EXTERNAL */)),
        _1jy/* sg0C */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1jx/* sg0x */), _/* EXTERNAL */)),
        _1jz/* sg0P */ = function(_/* EXTERNAL */, _1jA/* sg0R */){
          var _1jB/* sg0S */ = B(_L2/* FormEngine.JQuery.$wa26 */(_1jf/* sfZf */.b, _1jA/* sg0R */, _/* EXTERNAL */)),
          _1jC/* sg0Y */ = B(_1de/* FormEngine.JQuery.onMouseEnter1 */(function(_1jD/* sg0V */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jB/* sg0S */, _/* EXTERNAL */)),
          _1jE/* sg14 */ = B(_1hQ/* FormEngine.JQuery.onKeyup1 */(function(_1jF/* sg11 */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jC/* sg0Y */, _/* EXTERNAL */)),
          _1jG/* sg1a */ = B(_1hw/* FormEngine.JQuery.onBlur1 */(function(_1jH/* sg17 */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jE/* sg14 */, _/* EXTERNAL */));
          return new F(function(){return _1du/* FormEngine.JQuery.onMouseLeave1 */(function(_1jI/* sg1d */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jG/* sg1a */, _/* EXTERNAL */);});
        },
        _1jJ/* sg1g */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).c);
        if(!_1jJ/* sg1g */._){
          var _1jK/* sg1j */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _I/* GHC.Types.[] */, E(_1jy/* sg0C */), _/* EXTERNAL */));
          return new F(function(){return _1jz/* sg0P */(_/* EXTERNAL */, E(_1jK/* sg1j */));});
        }else{
          var _1jL/* sg1r */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1jJ/* sg1g */.a, E(_1jy/* sg0C */), _/* EXTERNAL */));
          return new F(function(){return _1jz/* sg0P */(_/* EXTERNAL */, E(_1jL/* sg1r */));});
        }
      };
      return new F(function(){return _1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1jw/* sg1w */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */);});
      break;
    case 3:
      var _1jM/* sg2D */ = function(_/* EXTERNAL */){
        var _1jN/* sg1E */ = B(_56/* FormEngine.JQuery.select1 */(_1hq/* FormEngine.FormElement.Rendering.lvl51 */, _/* EXTERNAL */)),
        _1jO/* sg1J */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1jN/* sg1E */), _/* EXTERNAL */)),
        _1jP/* sg1W */ = function(_/* EXTERNAL */, _1jQ/* sg1Y */){
          var _1jR/* sg1Z */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1jf/* sfZf */.b, _1jQ/* sg1Y */, _/* EXTERNAL */)),
          _1jS/* sg25 */ = B(_1de/* FormEngine.JQuery.onMouseEnter1 */(function(_1jT/* sg22 */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jR/* sg1Z */, _/* EXTERNAL */)),
          _1jU/* sg2b */ = B(_1hQ/* FormEngine.JQuery.onKeyup1 */(function(_1jV/* sg28 */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jS/* sg25 */, _/* EXTERNAL */)),
          _1jW/* sg2h */ = B(_1hw/* FormEngine.JQuery.onBlur1 */(function(_1jX/* sg2e */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jU/* sg2b */, _/* EXTERNAL */));
          return new F(function(){return _1du/* FormEngine.JQuery.onMouseLeave1 */(function(_1jY/* sg2k */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1jW/* sg2h */, _/* EXTERNAL */);});
        },
        _1jZ/* sg2n */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).c);
        if(!_1jZ/* sg2n */._){
          var _1k0/* sg2q */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _I/* GHC.Types.[] */, E(_1jO/* sg1J */), _/* EXTERNAL */));
          return new F(function(){return _1jP/* sg1W */(_/* EXTERNAL */, E(_1k0/* sg2q */));});
        }else{
          var _1k1/* sg2y */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1jZ/* sg2n */.a, E(_1jO/* sg1J */), _/* EXTERNAL */));
          return new F(function(){return _1jP/* sg1W */(_/* EXTERNAL */, E(_1k1/* sg2y */));});
        }
      };
      return new F(function(){return _1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1jM/* sg2D */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */);});
      break;
    case 4:
      var _1k2/* sg2E */ = _1jf/* sfZf */.a,
      _1k3/* sg2L */ = function(_1k4/* sg2M */, _/* EXTERNAL */){
        return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
      },
      _1k5/* sg8s */ = function(_/* EXTERNAL */){
        var _1k6/* sg2P */ = B(_56/* FormEngine.JQuery.select1 */(_1hp/* FormEngine.FormElement.Rendering.lvl50 */, _/* EXTERNAL */)),
        _1k7/* sg2U */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, _1je/* sfZe */, E(_1k6/* sg2P */), _/* EXTERNAL */)),
        _1k8/* sg2Z */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1k7/* sg2U */), _/* EXTERNAL */)),
        _1k9/* sg3c */ = function(_/* EXTERNAL */, _1ka/* sg3e */){
          var _1kb/* sg3f */ = function(_/* EXTERNAL */, _1kc/* sg3h */){
            var _1kd/* sg3l */ = B(_1de/* FormEngine.JQuery.onMouseEnter1 */(function(_1ke/* sg3i */, _/* EXTERNAL */){
              return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
            }, _1kc/* sg3h */, _/* EXTERNAL */)),
            _1kf/* sg3r */ = B(_1hQ/* FormEngine.JQuery.onKeyup1 */(function(_1kg/* sg3o */, _/* EXTERNAL */){
              return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
            }, _1kd/* sg3l */, _/* EXTERNAL */)),
            _1kh/* sg3x */ = B(_1hw/* FormEngine.JQuery.onBlur1 */(function(_1ki/* sg3u */, _/* EXTERNAL */){
              return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
            }, _1kf/* sg3r */, _/* EXTERNAL */)),
            _1kj/* sg3D */ = B(_1du/* FormEngine.JQuery.onMouseLeave1 */(function(_1kk/* sg3A */, _/* EXTERNAL */){
              return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
            }, _1kh/* sg3x */, _/* EXTERNAL */)),
            _1kl/* sg3I */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1ho/* FormEngine.FormElement.Rendering.lvl49 */, E(_1kj/* sg3D */), _/* EXTERNAL */)),
            _1km/* sg3L */ = E(_1k2/* sg2E */);
            if(_1km/* sg3L */._==3){
              var _1kn/* sg3P */ = E(_1km/* sg3L */.b);
              switch(_1kn/* sg3P */._){
                case 0:
                  return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1kn/* sg3P */.a, _1kl/* sg3I */, _/* EXTERNAL */);});
                  break;
                case 1:
                  var _1ko/* sg3S */ = new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1km/* sg3L */.a).b)), _Pq/* FormEngine.FormItem.nfiUnitId1 */));
                  }),
                  _1kp/* sg44 */ = E(_1kn/* sg3P */.a);
                  if(!_1kp/* sg44 */._){
                    return _1kl/* sg3I */;
                  }else{
                    var _1kq/* sg45 */ = _1kp/* sg44 */.a,
                    _1kr/* sg46 */ = _1kp/* sg44 */.b,
                    _1ks/* sg49 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hk/* FormEngine.FormElement.Rendering.lvl45 */, E(_1kl/* sg3I */), _/* EXTERNAL */)),
                    _1kt/* sg4e */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1kq/* sg45 */, E(_1ks/* sg49 */), _/* EXTERNAL */)),
                    _1ku/* sg4j */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1ko/* sg3S */, E(_1kt/* sg4e */), _/* EXTERNAL */)),
                    _1kv/* sg4o */ = B(_1dn/* FormEngine.JQuery.$wa30 */(_1jc/* sfZb */, E(_1ku/* sg4j */), _/* EXTERNAL */)),
                    _1kw/* sg4t */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1jc/* sfZb */, E(_1kv/* sg4o */), _/* EXTERNAL */)),
                    _1kx/* sg4y */ = B(_1dD/* FormEngine.JQuery.$wa31 */(_1k3/* sg2L */, E(_1kw/* sg4t */), _/* EXTERNAL */)),
                    _1ky/* sg4B */ = function(_/* EXTERNAL */, _1kz/* sg4D */){
                      var _1kA/* sg4E */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, _1kz/* sg4D */, _/* EXTERNAL */)),
                      _1kB/* sg4J */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1kq/* sg45 */, E(_1kA/* sg4E */), _/* EXTERNAL */));
                      return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hn/* FormEngine.FormElement.Rendering.lvl48 */, _1kB/* sg4J */, _/* EXTERNAL */);});
                    },
                    _1kC/* sg4M */ = E(_1jf/* sfZf */.c);
                    if(!_1kC/* sg4M */._){
                      var _1kD/* sg4P */ = B(_1ky/* sg4B */(_/* EXTERNAL */, E(_1kx/* sg4y */))),
                      _1kE/* sg4S */ = function(_1kF/* sg4T */, _1kG/* sg4U */, _/* EXTERNAL */){
                        while(1){
                          var _1kH/* sg4W */ = E(_1kF/* sg4T */);
                          if(!_1kH/* sg4W */._){
                            return _1kG/* sg4U */;
                          }else{
                            var _1kI/* sg4X */ = _1kH/* sg4W */.a,
                            _1kJ/* sg51 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hk/* FormEngine.FormElement.Rendering.lvl45 */, E(_1kG/* sg4U */), _/* EXTERNAL */)),
                            _1kK/* sg56 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1kI/* sg4X */, E(_1kJ/* sg51 */), _/* EXTERNAL */)),
                            _1kL/* sg5b */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1ko/* sg3S */, E(_1kK/* sg56 */), _/* EXTERNAL */)),
                            _1kM/* sg5g */ = B(_1dn/* FormEngine.JQuery.$wa30 */(_1jc/* sfZb */, E(_1kL/* sg5b */), _/* EXTERNAL */)),
                            _1kN/* sg5l */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1jc/* sfZb */, E(_1kM/* sg5g */), _/* EXTERNAL */)),
                            _1kO/* sg5q */ = B(_1dD/* FormEngine.JQuery.$wa31 */(_1k3/* sg2L */, E(_1kN/* sg5l */), _/* EXTERNAL */)),
                            _1kP/* sg5v */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, E(_1kO/* sg5q */), _/* EXTERNAL */)),
                            _1kQ/* sg5A */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1kI/* sg4X */, E(_1kP/* sg5v */), _/* EXTERNAL */)),
                            _1kR/* sg5F */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hn/* FormEngine.FormElement.Rendering.lvl48 */, E(_1kQ/* sg5A */), _/* EXTERNAL */));
                            _1kF/* sg4T */ = _1kH/* sg4W */.b;
                            _1kG/* sg4U */ = _1kR/* sg5F */;
                            continue;
                          }
                        }
                      };
                      return new F(function(){return _1kE/* sg4S */(_1kr/* sg46 */, _1kD/* sg4P */, _/* EXTERNAL */);});
                    }else{
                      var _1kS/* sg5I */ = _1kC/* sg4M */.a;
                      if(!B(_J9/* GHC.Base.eqString */(_1kS/* sg5I */, _1kq/* sg45 */))){
                        var _1kT/* sg5M */ = B(_1ky/* sg4B */(_/* EXTERNAL */, E(_1kx/* sg4y */))),
                        _1kU/* sg5P */ = function(_1kV/*  sg5Q */, _1kW/*  sg5R */, _/* EXTERNAL */){
                          while(1){
                            var _1kX/*  sg5P */ = B((function(_1kY/* sg5Q */, _1kZ/* sg5R */, _/* EXTERNAL */){
                              var _1l0/* sg5T */ = E(_1kY/* sg5Q */);
                              if(!_1l0/* sg5T */._){
                                return _1kZ/* sg5R */;
                              }else{
                                var _1l1/* sg5U */ = _1l0/* sg5T */.a,
                                _1l2/* sg5V */ = _1l0/* sg5T */.b,
                                _1l3/* sg5Y */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hk/* FormEngine.FormElement.Rendering.lvl45 */, E(_1kZ/* sg5R */), _/* EXTERNAL */)),
                                _1l4/* sg63 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1l1/* sg5U */, E(_1l3/* sg5Y */), _/* EXTERNAL */)),
                                _1l5/* sg68 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1ko/* sg3S */, E(_1l4/* sg63 */), _/* EXTERNAL */)),
                                _1l6/* sg6d */ = B(_1dn/* FormEngine.JQuery.$wa30 */(_1jc/* sfZb */, E(_1l5/* sg68 */), _/* EXTERNAL */)),
                                _1l7/* sg6i */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1jc/* sfZb */, E(_1l6/* sg6d */), _/* EXTERNAL */)),
                                _1l8/* sg6n */ = B(_1dD/* FormEngine.JQuery.$wa31 */(_1k3/* sg2L */, E(_1l7/* sg6i */), _/* EXTERNAL */)),
                                _1l9/* sg6q */ = function(_/* EXTERNAL */, _1la/* sg6s */){
                                  var _1lb/* sg6t */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, _1la/* sg6s */, _/* EXTERNAL */)),
                                  _1lc/* sg6y */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1l1/* sg5U */, E(_1lb/* sg6t */), _/* EXTERNAL */));
                                  return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hn/* FormEngine.FormElement.Rendering.lvl48 */, _1lc/* sg6y */, _/* EXTERNAL */);});
                                };
                                if(!B(_J9/* GHC.Base.eqString */(_1kS/* sg5I */, _1l1/* sg5U */))){
                                  var _1ld/* sg6E */ = B(_1l9/* sg6q */(_/* EXTERNAL */, E(_1l8/* sg6n */)));
                                  _1kV/*  sg5Q */ = _1l2/* sg5V */;
                                  _1kW/*  sg5R */ = _1ld/* sg6E */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1le/* sg6J */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1l8/* sg6n */), _/* EXTERNAL */)),
                                  _1lf/* sg6O */ = B(_1l9/* sg6q */(_/* EXTERNAL */, E(_1le/* sg6J */)));
                                  _1kV/*  sg5Q */ = _1l2/* sg5V */;
                                  _1kW/*  sg5R */ = _1lf/* sg6O */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1kV/*  sg5Q */, _1kW/*  sg5R */, _/* EXTERNAL */));
                            if(_1kX/*  sg5P */!=__continue/* EXTERNAL */){
                              return _1kX/*  sg5P */;
                            }
                          }
                        };
                        return new F(function(){return _1kU/* sg5P */(_1kr/* sg46 */, _1kT/* sg5M */, _/* EXTERNAL */);});
                      }else{
                        var _1lg/* sg6T */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1kx/* sg4y */), _/* EXTERNAL */)),
                        _1lh/* sg6Y */ = B(_1ky/* sg4B */(_/* EXTERNAL */, E(_1lg/* sg6T */))),
                        _1li/* sg71 */ = function(_1lj/*  sg72 */, _1lk/*  sg73 */, _/* EXTERNAL */){
                          while(1){
                            var _1ll/*  sg71 */ = B((function(_1lm/* sg72 */, _1ln/* sg73 */, _/* EXTERNAL */){
                              var _1lo/* sg75 */ = E(_1lm/* sg72 */);
                              if(!_1lo/* sg75 */._){
                                return _1ln/* sg73 */;
                              }else{
                                var _1lp/* sg76 */ = _1lo/* sg75 */.a,
                                _1lq/* sg77 */ = _1lo/* sg75 */.b,
                                _1lr/* sg7a */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hk/* FormEngine.FormElement.Rendering.lvl45 */, E(_1ln/* sg73 */), _/* EXTERNAL */)),
                                _1ls/* sg7f */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1lp/* sg76 */, E(_1lr/* sg7a */), _/* EXTERNAL */)),
                                _1lt/* sg7k */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1ko/* sg3S */, E(_1ls/* sg7f */), _/* EXTERNAL */)),
                                _1lu/* sg7p */ = B(_1dn/* FormEngine.JQuery.$wa30 */(_1jc/* sfZb */, E(_1lt/* sg7k */), _/* EXTERNAL */)),
                                _1lv/* sg7u */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1jc/* sfZb */, E(_1lu/* sg7p */), _/* EXTERNAL */)),
                                _1lw/* sg7z */ = B(_1dD/* FormEngine.JQuery.$wa31 */(_1k3/* sg2L */, E(_1lv/* sg7u */), _/* EXTERNAL */)),
                                _1lx/* sg7C */ = function(_/* EXTERNAL */, _1ly/* sg7E */){
                                  var _1lz/* sg7F */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, _1ly/* sg7E */, _/* EXTERNAL */)),
                                  _1lA/* sg7K */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1lp/* sg76 */, E(_1lz/* sg7F */), _/* EXTERNAL */));
                                  return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hn/* FormEngine.FormElement.Rendering.lvl48 */, _1lA/* sg7K */, _/* EXTERNAL */);});
                                };
                                if(!B(_J9/* GHC.Base.eqString */(_1kS/* sg5I */, _1lp/* sg76 */))){
                                  var _1lB/* sg7Q */ = B(_1lx/* sg7C */(_/* EXTERNAL */, E(_1lw/* sg7z */)));
                                  _1lj/*  sg72 */ = _1lq/* sg77 */;
                                  _1lk/*  sg73 */ = _1lB/* sg7Q */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1lC/* sg7V */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1lw/* sg7z */), _/* EXTERNAL */)),
                                  _1lD/* sg80 */ = B(_1lx/* sg7C */(_/* EXTERNAL */, E(_1lC/* sg7V */)));
                                  _1lj/*  sg72 */ = _1lq/* sg77 */;
                                  _1lk/*  sg73 */ = _1lD/* sg80 */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1lj/*  sg72 */, _1lk/*  sg73 */, _/* EXTERNAL */));
                            if(_1ll/*  sg71 */!=__continue/* EXTERNAL */){
                              return _1ll/*  sg71 */;
                            }
                          }
                        };
                        return new F(function(){return _1li/* sg71 */(_1kr/* sg46 */, _1lh/* sg6Y */, _/* EXTERNAL */);});
                      }
                    }
                  }
                  break;
                default:
                  return _1kl/* sg3I */;
              }
            }else{
              return E(_1bY/* FormEngine.FormItem.nfiUnit1 */);
            }
          },
          _1lE/* sg83 */ = E(_1jf/* sfZf */.b);
          if(!_1lE/* sg83 */._){
            var _1lF/* sg84 */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _I/* GHC.Types.[] */, _1ka/* sg3e */, _/* EXTERNAL */));
            return new F(function(){return _1kb/* sg3f */(_/* EXTERNAL */, _1lF/* sg84 */);});
          }else{
            var _1lG/* sg89 */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, B(_LS/* GHC.Float.$fShowFloat_$cshow */(_1lE/* sg83 */.a)), _1ka/* sg3e */, _/* EXTERNAL */));
            return new F(function(){return _1kb/* sg3f */(_/* EXTERNAL */, _1lG/* sg89 */);});
          }
        },
        _1lH/* sg8c */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1k2/* sg2E */)).c);
        if(!_1lH/* sg8c */._){
          var _1lI/* sg8f */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _I/* GHC.Types.[] */, E(_1k8/* sg2Z */), _/* EXTERNAL */));
          return new F(function(){return _1k9/* sg3c */(_/* EXTERNAL */, E(_1lI/* sg8f */));});
        }else{
          var _1lJ/* sg8n */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1lH/* sg8c */.a, E(_1k8/* sg2Z */), _/* EXTERNAL */));
          return new F(function(){return _1k9/* sg3c */(_/* EXTERNAL */, E(_1lJ/* sg8n */));});
        }
      };
      return new F(function(){return _1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1k5/* sg8s */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */);});
      break;
    case 5:
      var _1lK/* sg8x */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1eq/* FormEngine.FormElement.Rendering.lvl10 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1lL/* sg8F */ = B(_1dn/* FormEngine.JQuery.$wa30 */(function(_1lM/* sg8C */, _/* EXTERNAL */){
        return new F(function(){return _1ee/* FormEngine.FormElement.Rendering.a5 */(_1jf/* sfZf */, _/* EXTERNAL */);});
      }, E(_1lK/* sg8x */), _/* EXTERNAL */)),
      _1lN/* sg8N */ = B(_1dD/* FormEngine.JQuery.$wa31 */(function(_1lO/* sg8K */, _/* EXTERNAL */){
        return new F(function(){return _1e4/* FormEngine.FormElement.Rendering.a4 */(_1jf/* sfZf */, _/* EXTERNAL */);});
      }, E(_1lL/* sg8F */), _/* EXTERNAL */)),
      _1lP/* sg8S */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1lQ/* sg8V */ = __app1/* EXTERNAL */(_1lP/* sg8S */, E(_1lN/* sg8N */)),
      _1lR/* sg8Y */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1lS/* sg91 */ = __app1/* EXTERNAL */(_1lR/* sg8Y */, _1lQ/* sg8V */),
      _1lT/* sg94 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1er/* FormEngine.FormElement.Rendering.lvl11 */, _1lS/* sg91 */, _/* EXTERNAL */)),
      _1lU/* sg9a */ = __app1/* EXTERNAL */(_1lP/* sg8S */, E(_1lT/* sg94 */)),
      _1lV/* sg9e */ = __app1/* EXTERNAL */(_1lR/* sg8Y */, _1lU/* sg9a */),
      _1lW/* sg9h */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1es/* FormEngine.FormElement.Rendering.lvl12 */, _1lV/* sg9e */, _/* EXTERNAL */)),
      _1lX/* sg9n */ = __app1/* EXTERNAL */(_1lP/* sg8S */, E(_1lW/* sg9h */)),
      _1lY/* sg9r */ = __app1/* EXTERNAL */(_1lR/* sg8Y */, _1lX/* sg9n */),
      _1lZ/* sg9u */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hm/* FormEngine.FormElement.Rendering.lvl47 */, _1lY/* sg9r */, _/* EXTERNAL */)),
      _1m0/* sg9D */ = B(_Il/* FormEngine.JQuery.$wa34 */(new T(function(){
        var _1m1/* sg9z */ = E(_1jf/* sfZf */.a);
        if(_1m1/* sg9z */._==4){
          return E(_1m1/* sg9z */.b);
        }else{
          return E(_1g0/* FormEngine.FormItem.ifiText1 */);
        }
      },1), E(_1lZ/* sg9u */), _/* EXTERNAL */)),
      _1m2/* sg9I */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
      _1m3/* sg9L */ = __app1/* EXTERNAL */(_1m2/* sg9I */, E(_1m0/* sg9D */)),
      _1m4/* sg9P */ = __app1/* EXTERNAL */(_1m2/* sg9I */, _1m3/* sg9L */),
      _1m5/* sg9T */ = __app1/* EXTERNAL */(_1m2/* sg9I */, _1m4/* sg9P */);
      return new F(function(){return _1dN/* FormEngine.FormElement.Rendering.a1 */(_1jf/* sfZf */, _1m5/* sg9T */, _/* EXTERNAL */);});
      break;
    case 6:
      var _1m6/* sg9Y */ = _1jf/* sfZf */.b,
      _1m7/* sga3 */ = new T(function(){
        var _1m8/* sgae */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).c);
        if(!_1m8/* sgae */._){
          return __Z/* EXTERNAL */;
        }else{
          return E(_1m8/* sgae */.a);
        }
      }),
      _1m9/* sgag */ = new T(function(){
        return B(_1fW/* FormEngine.FormElement.Rendering.go */(_1m6/* sg9Y */, _1ge/* GHC.List.last1 */));
      }),
      _1ma/* sgah */ = function(_1mb/* sgai */, _/* EXTERNAL */){
        return new F(function(){return _56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1h8/* FormEngine.FormElement.Rendering.lvl33 */, new T(function(){
          return B(_12/* GHC.Base.++ */(B(_1ip/* FormEngine.FormElement.Identifiers.radioId */(_1jf/* sfZf */, _1mb/* sgai */)), _1i4/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
        },1))), _/* EXTERNAL */);});
      },
      _1mc/* sgan */ = function(_1md/* sgao */, _/* EXTERNAL */){
        while(1){
          var _1me/* sgaq */ = E(_1md/* sgao */);
          if(!_1me/* sgaq */._){
            return _I/* GHC.Types.[] */;
          }else{
            var _1mf/* sgas */ = _1me/* sgaq */.b,
            _1mg/* sgat */ = E(_1me/* sgaq */.a);
            if(!_1mg/* sgat */._){
              _1md/* sgao */ = _1mf/* sgas */;
              continue;
            }else{
              var _1mh/* sgaz */ = B(_1ma/* sgah */(_1mg/* sgat */, _/* EXTERNAL */)),
              _1mi/* sgaC */ = B(_1mc/* sgan */(_1mf/* sgas */, _/* EXTERNAL */));
              return new T2(1,_1mh/* sgaz */,_1mi/* sgaC */);
            }
          }
        }
      },
      _1mj/* sgaG */ = function(_1mk/* sgaH */, _/* EXTERNAL */){
        var _1ml/* sgaJ */ = B(_1g3/* FormEngine.JQuery.isRadioSelected1 */(_1je/* sfZe */, _/* EXTERNAL */));
        return new F(function(){return _1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ml/* sgaJ */, _/* EXTERNAL */);});
      },
      _1mm/* sgdl */ = function(_/* EXTERNAL */){
        var _1mn/* sgaN */ = B(_56/* FormEngine.JQuery.select1 */(_1hl/* FormEngine.FormElement.Rendering.lvl46 */, _/* EXTERNAL */)),
        _1mo/* sgaQ */ = function(_1mp/*  sgaR */, _1mq/*  sgaS */, _/* EXTERNAL */){
          while(1){
            var _1mr/*  sgaQ */ = B((function(_1ms/* sgaR */, _1mt/* sgaS */, _/* EXTERNAL */){
              var _1mu/* sgaU */ = E(_1ms/* sgaR */);
              if(!_1mu/* sgaU */._){
                return _1mt/* sgaS */;
              }else{
                var _1mv/* sgaV */ = _1mu/* sgaU */.a,
                _1mw/* sgaW */ = _1mu/* sgaU */.b,
                _1mx/* sgaZ */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hk/* FormEngine.FormElement.Rendering.lvl45 */, E(_1mt/* sgaS */), _/* EXTERNAL */)),
                _1my/* sgb5 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, new T(function(){
                  return B(_1ip/* FormEngine.FormElement.Identifiers.radioId */(_1jf/* sfZf */, _1mv/* sgaV */));
                },1), E(_1mx/* sgaZ */), _/* EXTERNAL */)),
                _1mz/* sgba */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1my/* sgb5 */), _/* EXTERNAL */)),
                _1mA/* sgbf */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1m7/* sga3 */, E(_1mz/* sgba */), _/* EXTERNAL */)),
                _1mB/* sgbl */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, new T(function(){
                  return B(_1hZ/* FormEngine.FormElement.FormElement.optionElemValue */(_1mv/* sgaV */));
                },1), E(_1mA/* sgbf */), _/* EXTERNAL */)),
                _1mC/* sgbo */ = function(_/* EXTERNAL */, _1mD/* sgbq */){
                  var _1mE/* sgbU */ = B(_1d7/* FormEngine.JQuery.$wa23 */(function(_1mF/* sgbr */, _/* EXTERNAL */){
                    var _1mG/* sgbt */ = B(_1mc/* sgan */(_1m6/* sg9Y */, _/* EXTERNAL */)),
                    _1mH/* sgbw */ = B(_1fH/* FormEngine.FormElement.Rendering.a7 */(_1mG/* sgbt */, _/* EXTERNAL */)),
                    _1mI/* sgbz */ = E(_1mv/* sgaV */);
                    if(!_1mI/* sgbz */._){
                      var _1mJ/* sgbC */ = B(_1g3/* FormEngine.JQuery.isRadioSelected1 */(_1je/* sfZe */, _/* EXTERNAL */));
                      return new F(function(){return _1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1mJ/* sgbC */, _/* EXTERNAL */);});
                    }else{
                      var _1mK/* sgbI */ = B(_1ma/* sgah */(_1mI/* sgbz */, _/* EXTERNAL */)),
                      _1mL/* sgbN */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _IW/* FormEngine.JQuery.appearJq2 */, E(_1mK/* sgbI */), _/* EXTERNAL */)),
                      _1mM/* sgbQ */ = B(_1g3/* FormEngine.JQuery.isRadioSelected1 */(_1je/* sfZe */, _/* EXTERNAL */));
                      return new F(function(){return _1aK/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1mM/* sgbQ */, _/* EXTERNAL */);});
                    }
                  }, _1mD/* sgbq */, _/* EXTERNAL */)),
                  _1mN/* sgbZ */ = B(_1dD/* FormEngine.JQuery.$wa31 */(_1mj/* sgaG */, E(_1mE/* sgbU */), _/* EXTERNAL */)),
                  _1mO/* sgc4 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dS/* FormEngine.FormElement.Rendering.lvl6 */, E(_1mN/* sgbZ */), _/* EXTERNAL */)),
                  _1mP/* sgca */ = B(_Il/* FormEngine.JQuery.$wa34 */(new T(function(){
                    return B(_1hZ/* FormEngine.FormElement.FormElement.optionElemValue */(_1mv/* sgaV */));
                  },1), E(_1mO/* sgc4 */), _/* EXTERNAL */)),
                  _1mQ/* sgcd */ = E(_1mv/* sgaV */);
                  if(!_1mQ/* sgcd */._){
                    var _1mR/* sgce */ = _1mQ/* sgcd */.a,
                    _1mS/* sgci */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1mP/* sgca */), _/* EXTERNAL */)),
                    _1mT/* sgcl */ = E(_1m9/* sgag */);
                    if(!_1mT/* sgcl */._){
                      if(!B(_LK/* FormEngine.FormItem.$fEqOption_$c== */(_1mR/* sgce */, _1mT/* sgcl */.a))){
                        return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hj/* FormEngine.FormElement.Rendering.lvl44 */, _1mS/* sgci */, _/* EXTERNAL */);});
                      }else{
                        return _1mS/* sgci */;
                      }
                    }else{
                      if(!B(_LK/* FormEngine.FormItem.$fEqOption_$c== */(_1mR/* sgce */, _1mT/* sgcl */.a))){
                        return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hj/* FormEngine.FormElement.Rendering.lvl44 */, _1mS/* sgci */, _/* EXTERNAL */);});
                      }else{
                        return _1mS/* sgci */;
                      }
                    }
                  }else{
                    var _1mU/* sgct */ = _1mQ/* sgcd */.a,
                    _1mV/* sgcy */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h7/* FormEngine.FormElement.Rendering.lvl32 */, E(_1mP/* sgca */), _/* EXTERNAL */)),
                    _1mW/* sgcB */ = E(_1m9/* sgag */);
                    if(!_1mW/* sgcB */._){
                      if(!B(_LK/* FormEngine.FormItem.$fEqOption_$c== */(_1mU/* sgct */, _1mW/* sgcB */.a))){
                        return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hj/* FormEngine.FormElement.Rendering.lvl44 */, _1mV/* sgcy */, _/* EXTERNAL */);});
                      }else{
                        return _1mV/* sgcy */;
                      }
                    }else{
                      if(!B(_LK/* FormEngine.FormItem.$fEqOption_$c== */(_1mU/* sgct */, _1mW/* sgcB */.a))){
                        return new F(function(){return _1fN/* FormEngine.JQuery.appendT1 */(_1hj/* FormEngine.FormElement.Rendering.lvl44 */, _1mV/* sgcy */, _/* EXTERNAL */);});
                      }else{
                        return _1mV/* sgcy */;
                      }
                    }
                  }
                },
                _1mX/* sgcJ */ = E(_1mv/* sgaV */);
                if(!_1mX/* sgcJ */._){
                  if(!E(_1mX/* sgcJ */.b)){
                    var _1mY/* sgcP */ = B(_1mC/* sgbo */(_/* EXTERNAL */, E(_1mB/* sgbl */)));
                    _1mp/*  sgaR */ = _1mw/* sgaW */;
                    _1mq/*  sgaS */ = _1mY/* sgcP */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1mZ/* sgcU */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1mB/* sgbl */), _/* EXTERNAL */)),
                    _1n0/* sgcZ */ = B(_1mC/* sgbo */(_/* EXTERNAL */, E(_1mZ/* sgcU */)));
                    _1mp/*  sgaR */ = _1mw/* sgaW */;
                    _1mq/*  sgaS */ = _1n0/* sgcZ */;
                    return __continue/* EXTERNAL */;
                  }
                }else{
                  if(!E(_1mX/* sgcJ */.b)){
                    var _1n1/* sgd8 */ = B(_1mC/* sgbo */(_/* EXTERNAL */, E(_1mB/* sgbl */)));
                    _1mp/*  sgaR */ = _1mw/* sgaW */;
                    _1mq/*  sgaS */ = _1n1/* sgd8 */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1n2/* sgdd */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1mB/* sgbl */), _/* EXTERNAL */)),
                    _1n3/* sgdi */ = B(_1mC/* sgbo */(_/* EXTERNAL */, E(_1n2/* sgdd */)));
                    _1mp/*  sgaR */ = _1mw/* sgaW */;
                    _1mq/*  sgaS */ = _1n3/* sgdi */;
                    return __continue/* EXTERNAL */;
                  }
                }
              }
            })(_1mp/*  sgaR */, _1mq/*  sgaS */, _/* EXTERNAL */));
            if(_1mr/*  sgaQ */!=__continue/* EXTERNAL */){
              return _1mr/*  sgaQ */;
            }
          }
        };
        return new F(function(){return _1mo/* sgaQ */(_1m6/* sg9Y */, _1mn/* sgaN */, _/* EXTERNAL */);});
      },
      _1n4/* sgdm */ = B(_1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1mm/* sgdl */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1n5/* sgdp */ = function(_1n6/* sgdq */, _1n7/* sgdr */, _/* EXTERNAL */){
        while(1){
          var _1n8/* sgdt */ = E(_1n6/* sgdq */);
          if(!_1n8/* sgdt */._){
            return _1n7/* sgdr */;
          }else{
            var _1n9/* sgdw */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1n8/* sgdt */.a, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1n7/* sgdr */, _/* EXTERNAL */));
            _1n6/* sgdq */ = _1n8/* sgdt */.b;
            _1n7/* sgdr */ = _1n9/* sgdw */;
            continue;
          }
        }
      },
      _1na/* sgdz */ = function(_1nb/*  sgdA */, _1nc/*  sgdB */, _/* EXTERNAL */){
        while(1){
          var _1nd/*  sgdz */ = B((function(_1ne/* sgdA */, _1nf/* sgdB */, _/* EXTERNAL */){
            var _1ng/* sgdD */ = E(_1ne/* sgdA */);
            if(!_1ng/* sgdD */._){
              return _1nf/* sgdB */;
            }else{
              var _1nh/* sgdF */ = _1ng/* sgdD */.b,
              _1ni/* sgdG */ = E(_1ng/* sgdD */.a);
              if(!_1ni/* sgdG */._){
                var _1nj/*   sgdB */ = _1nf/* sgdB */;
                _1nb/*  sgdA */ = _1nh/* sgdF */;
                _1nc/*  sgdB */ = _1nj/*   sgdB */;
                return __continue/* EXTERNAL */;
              }else{
                var _1nk/* sgdO */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hi/* FormEngine.FormElement.Rendering.lvl43 */, E(_1nf/* sgdB */), _/* EXTERNAL */)),
                _1nl/* sgdV */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_1ip/* FormEngine.FormElement.Identifiers.radioId */(_1jf/* sfZf */, _1ni/* sgdG */)), _1i4/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                },1), E(_1nk/* sgdO */), _/* EXTERNAL */)),
                _1nm/* sge0 */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
                _1nn/* sge3 */ = __app1/* EXTERNAL */(_1nm/* sge0 */, E(_1nl/* sgdV */)),
                _1no/* sge6 */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
                _1np/* sge9 */ = __app1/* EXTERNAL */(_1no/* sge6 */, _1nn/* sge3 */),
                _1nq/* sgec */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, _1np/* sge9 */, _/* EXTERNAL */)),
                _1nr/* sgef */ = B(_1n5/* sgdp */(_1ni/* sgdG */.c, _1nq/* sgec */, _/* EXTERNAL */)),
                _1ns/* sgek */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
                _1nt/* sgen */ = __app1/* EXTERNAL */(_1ns/* sgek */, E(_1nr/* sgef */)),
                _1nu/* sgeq */ = function(_1nv/*  sger */, _1nw/*  sges */, _1nx/*  sfrT */, _/* EXTERNAL */){
                  while(1){
                    var _1ny/*  sgeq */ = B((function(_1nz/* sger */, _1nA/* sges */, _1nB/* sfrT */, _/* EXTERNAL */){
                      var _1nC/* sgeu */ = E(_1nz/* sger */);
                      if(!_1nC/* sgeu */._){
                        return _1nA/* sges */;
                      }else{
                        var _1nD/* sgex */ = _1nC/* sgeu */.b,
                        _1nE/* sgey */ = E(_1nC/* sgeu */.a);
                        if(!_1nE/* sgey */._){
                          var _1nF/*   sges */ = _1nA/* sges */,
                          _1nG/*   sfrT */ = _/* EXTERNAL */;
                          _1nv/*  sger */ = _1nD/* sgex */;
                          _1nw/*  sges */ = _1nF/*   sges */;
                          _1nx/*  sfrT */ = _1nG/*   sfrT */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _1nH/* sgeE */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hi/* FormEngine.FormElement.Rendering.lvl43 */, _1nA/* sges */, _/* EXTERNAL */)),
                          _1nI/* sgeL */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, new T(function(){
                            return B(_12/* GHC.Base.++ */(B(_1ip/* FormEngine.FormElement.Identifiers.radioId */(_1jf/* sfZf */, _1nE/* sgey */)), _1i4/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                          },1), E(_1nH/* sgeE */), _/* EXTERNAL */)),
                          _1nJ/* sgeR */ = __app1/* EXTERNAL */(_1nm/* sge0 */, E(_1nI/* sgeL */)),
                          _1nK/* sgeV */ = __app1/* EXTERNAL */(_1no/* sge6 */, _1nJ/* sgeR */),
                          _1nL/* sgeY */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, _1nK/* sgeV */, _/* EXTERNAL */)),
                          _1nM/* sgf1 */ = B(_1n5/* sgdp */(_1nE/* sgey */.c, _1nL/* sgeY */, _/* EXTERNAL */)),
                          _1nN/* sgf7 */ = __app1/* EXTERNAL */(_1ns/* sgek */, E(_1nM/* sgf1 */)),
                          _1nG/*   sfrT */ = _/* EXTERNAL */;
                          _1nv/*  sger */ = _1nD/* sgex */;
                          _1nw/*  sges */ = _1nN/* sgf7 */;
                          _1nx/*  sfrT */ = _1nG/*   sfrT */;
                          return __continue/* EXTERNAL */;
                        }
                      }
                    })(_1nv/*  sger */, _1nw/*  sges */, _1nx/*  sfrT */, _/* EXTERNAL */));
                    if(_1ny/*  sgeq */!=__continue/* EXTERNAL */){
                      return _1ny/*  sgeq */;
                    }
                  }
                };
                return new F(function(){return _1nu/* sgeq */(_1nh/* sgdF */, _1nt/* sgen */, _/* EXTERNAL */, _/* EXTERNAL */);});
              }
            }
          })(_1nb/*  sgdA */, _1nc/*  sgdB */, _/* EXTERNAL */));
          if(_1nd/*  sgdz */!=__continue/* EXTERNAL */){
            return _1nd/*  sgdz */;
          }
        }
      };
      return new F(function(){return _1na/* sgdz */(_1m6/* sg9Y */, _1n4/* sgdm */, _/* EXTERNAL */);});
      break;
    case 7:
      var _1nO/* sgfa */ = _1jf/* sfZf */.a,
      _1nP/* sgi2 */ = function(_/* EXTERNAL */){
        var _1nQ/* sgfh */ = B(_56/* FormEngine.JQuery.select1 */(_1hh/* FormEngine.FormElement.Rendering.lvl42 */, _/* EXTERNAL */)),
        _1nR/* sgfm */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1nQ/* sgfh */), _/* EXTERNAL */)),
        _1nS/* sgfz */ = function(_/* EXTERNAL */, _1nT/* sgfB */){
          var _1nU/* sgfF */ = B(_1hw/* FormEngine.JQuery.onBlur1 */(function(_1nV/* sgfC */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1nT/* sgfB */, _/* EXTERNAL */)),
          _1nW/* sgfL */ = B(_1hG/* FormEngine.JQuery.onChange1 */(function(_1nX/* sgfI */, _/* EXTERNAL */){
            return new F(function(){return _1cM/* FormEngine.FormElement.Rendering.$wa1 */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1nU/* sgfF */, _/* EXTERNAL */)),
          _1nY/* sgfR */ = B(_1du/* FormEngine.JQuery.onMouseLeave1 */(function(_1nZ/* sgfO */, _/* EXTERNAL */){
            return new F(function(){return _1cE/* FormEngine.FormElement.Rendering.$wa */(_1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _/* EXTERNAL */);});
          }, _1nW/* sgfL */, _/* EXTERNAL */)),
          _1o0/* sgfU */ = E(_1nO/* sgfa */);
          if(_1o0/* sgfU */._==6){
            var _1o1/* sgfY */ = E(_1o0/* sgfU */.b);
            if(!_1o1/* sgfY */._){
              return _1nY/* sgfR */;
            }else{
              var _1o2/* sgg0 */ = _1o1/* sgfY */.b,
              _1o3/* sgg1 */ = E(_1o1/* sgfY */.a),
              _1o4/* sgg2 */ = _1o3/* sgg1 */.a,
              _1o5/* sgg6 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hf/* FormEngine.FormElement.Rendering.lvl40 */, E(_1nY/* sgfR */), _/* EXTERNAL */)),
              _1o6/* sggb */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1o4/* sgg2 */, E(_1o5/* sgg6 */), _/* EXTERNAL */)),
              _1o7/* sggg */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1o3/* sgg1 */.b, E(_1o6/* sggb */), _/* EXTERNAL */)),
              _1o8/* sggj */ = E(_1jf/* sfZf */.b);
              if(!_1o8/* sggj */._){
                var _1o9/* sggk */ = function(_1oa/* sggl */, _1ob/* sggm */, _/* EXTERNAL */){
                  while(1){
                    var _1oc/* sggo */ = E(_1oa/* sggl */);
                    if(!_1oc/* sggo */._){
                      return _1ob/* sggm */;
                    }else{
                      var _1od/* sggr */ = E(_1oc/* sggo */.a),
                      _1oe/* sggw */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hf/* FormEngine.FormElement.Rendering.lvl40 */, E(_1ob/* sggm */), _/* EXTERNAL */)),
                      _1of/* sggB */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1od/* sggr */.a, E(_1oe/* sggw */), _/* EXTERNAL */)),
                      _1og/* sggG */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1od/* sggr */.b, E(_1of/* sggB */), _/* EXTERNAL */));
                      _1oa/* sggl */ = _1oc/* sggo */.b;
                      _1ob/* sggm */ = _1og/* sggG */;
                      continue;
                    }
                  }
                };
                return new F(function(){return _1o9/* sggk */(_1o2/* sgg0 */, _1o7/* sggg */, _/* EXTERNAL */);});
              }else{
                var _1oh/* sggJ */ = _1o8/* sggj */.a;
                if(!B(_J9/* GHC.Base.eqString */(_1o4/* sgg2 */, _1oh/* sggJ */))){
                  var _1oi/* sggL */ = function(_1oj/* sggM */, _1ok/* sggN */, _/* EXTERNAL */){
                    while(1){
                      var _1ol/* sggP */ = E(_1oj/* sggM */);
                      if(!_1ol/* sggP */._){
                        return _1ok/* sggN */;
                      }else{
                        var _1om/* sggR */ = _1ol/* sggP */.b,
                        _1on/* sggS */ = E(_1ol/* sggP */.a),
                        _1oo/* sggT */ = _1on/* sggS */.a,
                        _1op/* sggX */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hf/* FormEngine.FormElement.Rendering.lvl40 */, E(_1ok/* sggN */), _/* EXTERNAL */)),
                        _1oq/* sgh2 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1oo/* sggT */, E(_1op/* sggX */), _/* EXTERNAL */)),
                        _1or/* sgh7 */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1on/* sggS */.b, E(_1oq/* sgh2 */), _/* EXTERNAL */));
                        if(!B(_J9/* GHC.Base.eqString */(_1oo/* sggT */, _1oh/* sggJ */))){
                          _1oj/* sggM */ = _1om/* sggR */;
                          _1ok/* sggN */ = _1or/* sgh7 */;
                          continue;
                        }else{
                          var _1os/* sghd */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1he/* FormEngine.FormElement.Rendering.lvl39 */, _1he/* FormEngine.FormElement.Rendering.lvl39 */, E(_1or/* sgh7 */), _/* EXTERNAL */));
                          _1oj/* sggM */ = _1om/* sggR */;
                          _1ok/* sggN */ = _1os/* sghd */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1oi/* sggL */(_1o2/* sgg0 */, _1o7/* sggg */, _/* EXTERNAL */);});
                }else{
                  var _1ot/* sghi */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1he/* FormEngine.FormElement.Rendering.lvl39 */, _1he/* FormEngine.FormElement.Rendering.lvl39 */, E(_1o7/* sggg */), _/* EXTERNAL */)),
                  _1ou/* sghl */ = function(_1ov/* sghm */, _1ow/* sghn */, _/* EXTERNAL */){
                    while(1){
                      var _1ox/* sghp */ = E(_1ov/* sghm */);
                      if(!_1ox/* sghp */._){
                        return _1ow/* sghn */;
                      }else{
                        var _1oy/* sghr */ = _1ox/* sghp */.b,
                        _1oz/* sghs */ = E(_1ox/* sghp */.a),
                        _1oA/* sght */ = _1oz/* sghs */.a,
                        _1oB/* sghx */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hf/* FormEngine.FormElement.Rendering.lvl40 */, E(_1ow/* sghn */), _/* EXTERNAL */)),
                        _1oC/* sghC */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, _1oA/* sght */, E(_1oB/* sghx */), _/* EXTERNAL */)),
                        _1oD/* sghH */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1oz/* sghs */.b, E(_1oC/* sghC */), _/* EXTERNAL */));
                        if(!B(_J9/* GHC.Base.eqString */(_1oA/* sght */, _1oh/* sggJ */))){
                          _1ov/* sghm */ = _1oy/* sghr */;
                          _1ow/* sghn */ = _1oD/* sghH */;
                          continue;
                        }else{
                          var _1oE/* sghN */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1he/* FormEngine.FormElement.Rendering.lvl39 */, _1he/* FormEngine.FormElement.Rendering.lvl39 */, E(_1oD/* sghH */), _/* EXTERNAL */));
                          _1ov/* sghm */ = _1oy/* sghr */;
                          _1ow/* sghn */ = _1oE/* sghN */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1ou/* sghl */(_1o2/* sgg0 */, _1ot/* sghi */, _/* EXTERNAL */);});
                }
              }
            }
          }else{
            return E(_1gf/* FormEngine.FormItem.lfiAvailableOptions1 */);
          }
        },
        _1oF/* sghQ */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1nO/* sgfa */)).c);
        if(!_1oF/* sghQ */._){
          var _1oG/* sghT */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _I/* GHC.Types.[] */, E(_1nR/* sgfm */), _/* EXTERNAL */));
          return new F(function(){return _1nS/* sgfz */(_/* EXTERNAL */, _1oG/* sghT */);});
        }else{
          var _1oH/* sghZ */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1hg/* FormEngine.FormElement.Rendering.lvl41 */, _1oF/* sghQ */.a, E(_1nR/* sgfm */), _/* EXTERNAL */));
          return new F(function(){return _1nS/* sgfz */(_/* EXTERNAL */, _1oH/* sghZ */);});
        }
      };
      return new F(function(){return _1ex/* FormEngine.FormElement.Rendering.$wa2 */(_1nP/* sgi2 */, _1jf/* sfZf */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */);});
      break;
    case 8:
      var _1oI/* sgi3 */ = _1jf/* sfZf */.a,
      _1oJ/* sgi9 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hd/* FormEngine.FormElement.Rendering.lvl38 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1oK/* sgie */ = new T(function(){
        var _1oL/* sgif */ = E(_1oI/* sgi3 */);
        switch(_1oL/* sgif */._){
          case 8:
            return E(_1oL/* sgif */.b);
            break;
          case 9:
            return E(_1oL/* sgif */.b);
            break;
          case 10:
            return E(_1oL/* sgif */.b);
            break;
          default:
            return E(_5U/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _1oM/* sgiq */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h1/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_4A/* GHC.Show.$fShowInt_$cshow */(_1oK/* sgie */));
      },1), E(_1oJ/* sgi9 */), _/* EXTERNAL */)),
      _1oN/* sgit */ = E(_1oK/* sgie */),
      _1oO/* sgiv */ = function(_/* EXTERNAL */, _1oP/* sgix */){
        var _1oQ/* sgiB */ = __app1/* EXTERNAL */(E(_I0/* FormEngine.JQuery.addClassInside_f3 */), _1oP/* sgix */),
        _1oR/* sgiH */ = __app1/* EXTERNAL */(E(_HZ/* FormEngine.JQuery.addClassInside_f2 */), _1oQ/* sgiB */),
        _1oS/* sgiK */ = B(_4r/* FormEngine.FormItem.fiDescriptor */(_1oI/* sgi3 */)),
        _1oT/* sgiV */ = B(_1fp/* FormEngine.FormElement.Rendering.a2 */(_1oS/* sgiK */.a, _1oN/* sgit */, _1oR/* sgiH */, _/* EXTERNAL */)),
        _1oU/* sgiY */ = function(_/* EXTERNAL */, _1oV/* sgj0 */){
          var _1oW/* sgj1 */ = function(_1oX/* sgj2 */, _1oY/* sgj3 */, _/* EXTERNAL */){
            while(1){
              var _1oZ/* sgj5 */ = E(_1oX/* sgj2 */);
              if(!_1oZ/* sgj5 */._){
                return _1oY/* sgj3 */;
              }else{
                var _1p0/* sgj8 */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1oZ/* sgj5 */.a, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1oY/* sgj3 */, _/* EXTERNAL */));
                _1oX/* sgj2 */ = _1oZ/* sgj5 */.b;
                _1oY/* sgj3 */ = _1p0/* sgj8 */;
                continue;
              }
            }
          },
          _1p1/* sgjb */ = B(_1oW/* sgj1 */(_1jf/* sfZf */.b, _1oV/* sgj0 */, _/* EXTERNAL */));
          return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1p1/* sgjb */));});
        },
        _1p2/* sgjn */ = E(_1oS/* sgiK */.e);
        if(!_1p2/* sgjn */._){
          return new F(function(){return _1oU/* sgiY */(_/* EXTERNAL */, _1oT/* sgiV */);});
        }else{
          var _1p3/* sgjr */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dJ/* FormEngine.FormElement.Rendering.lvl3 */, E(_1oT/* sgiV */), _/* EXTERNAL */)),
          _1p4/* sgjw */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1p2/* sgjn */.a, E(_1p3/* sgjr */), _/* EXTERNAL */));
          return new F(function(){return _1oU/* sgiY */(_/* EXTERNAL */, _1p4/* sgjw */);});
        }
      };
      if(_1oN/* sgit */<=1){
        return new F(function(){return _1oO/* sgiv */(_/* EXTERNAL */, E(_1oM/* sgiq */));});
      }else{
        var _1p5/* sgjF */ = B(_1cU/* FormEngine.JQuery.$wa1 */(_1h2/* FormEngine.FormElement.Rendering.lvl27 */, E(_1oM/* sgiq */), _/* EXTERNAL */));
        return new F(function(){return _1oO/* sgiv */(_/* EXTERNAL */, E(_1p5/* sgjF */));});
      }
      break;
    case 9:
      var _1p6/* sgjK */ = _1jf/* sfZf */.a,
      _1p7/* sgjM */ = _1jf/* sfZf */.c,
      _1p8/* sgjR */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hc/* FormEngine.FormElement.Rendering.lvl37 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1p9/* sgkd */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h1/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        var _1pa/* sgjW */ = E(_1p6/* sgjK */);
        switch(_1pa/* sgjW */._){
          case 8:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1pa/* sgjW */.b), _I/* GHC.Types.[] */));
            break;
          case 9:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1pa/* sgjW */.b), _I/* GHC.Types.[] */));
            break;
          case 10:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1pa/* sgjW */.b), _I/* GHC.Types.[] */));
            break;
          default:
            return E(_1hu/* FormEngine.FormElement.Rendering.lvl55 */);
        }
      },1), E(_1p8/* sgjR */), _/* EXTERNAL */)),
      _1pb/* sgkl */ = B(_1dn/* FormEngine.JQuery.$wa30 */(function(_1pc/* sgki */, _/* EXTERNAL */){
        return new F(function(){return _1ee/* FormEngine.FormElement.Rendering.a5 */(_1jf/* sfZf */, _/* EXTERNAL */);});
      }, E(_1p9/* sgkd */), _/* EXTERNAL */)),
      _1pd/* sgkt */ = B(_1dD/* FormEngine.JQuery.$wa31 */(function(_1pe/* sgkq */, _/* EXTERNAL */){
        return new F(function(){return _1e4/* FormEngine.FormElement.Rendering.a4 */(_1jf/* sfZf */, _/* EXTERNAL */);});
      }, E(_1pb/* sgkl */), _/* EXTERNAL */)),
      _1pf/* sgky */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1pg/* sgkB */ = __app1/* EXTERNAL */(_1pf/* sgky */, E(_1pd/* sgkt */)),
      _1ph/* sgkE */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1pi/* sgkH */ = __app1/* EXTERNAL */(_1ph/* sgkE */, _1pg/* sgkB */),
      _1pj/* sgkK */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1hb/* FormEngine.FormElement.Rendering.lvl36 */, _1pi/* sgkH */, _/* EXTERNAL */)),
      _1pk/* sgkP */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ha/* FormEngine.FormElement.Rendering.lvl35 */, _1je/* sfZe */, E(_1pj/* sgkK */), _/* EXTERNAL */)),
      _1pl/* sgkS */ = function(_/* EXTERNAL */, _1pm/* sgkU */){
        var _1pn/* sgkV */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_1h8/* FormEngine.FormElement.Rendering.lvl33 */, new T(function(){
            return B(_12/* GHC.Base.++ */(_1je/* sfZe */, _1fQ/* FormEngine.FormElement.Identifiers.checkboxId1 */));
          },1)));
        }),
        _1po/* sgls */ = B(_1d7/* FormEngine.JQuery.$wa23 */(function(_1pp/* sgkX */, _/* EXTERNAL */){
          var _1pq/* sgkZ */ = B(_56/* FormEngine.JQuery.select1 */(_1pn/* sgkV */, _/* EXTERNAL */)),
          _1pr/* sgl7 */ = __app1/* EXTERNAL */(E(_1fv/* FormEngine.JQuery.target_f1 */), E(_1pp/* sgkX */)),
          _1ps/* sgld */ = __app1/* EXTERNAL */(E(_1g1/* FormEngine.JQuery.isChecked_f1 */), _1pr/* sgl7 */);
          if(!_1ps/* sgld */){
            var _1pt/* sglj */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _Jt/* FormEngine.JQuery.disappearJq2 */, E(_1pq/* sgkZ */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _1pu/* sglo */ = B(_43/* FormEngine.JQuery.$wa2 */(_IX/* FormEngine.JQuery.appearJq3 */, _IW/* FormEngine.JQuery.appearJq2 */, E(_1pq/* sgkZ */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        }, _1pm/* sgkU */, _/* EXTERNAL */)),
        _1pv/* sglv */ = B(_1dV/* FormEngine.FormElement.Rendering.a3 */(_1jf/* sfZf */, _1po/* sgls */, _/* EXTERNAL */)),
        _1pw/* sgly */ = function(_/* EXTERNAL */, _1px/* sglA */){
          var _1py/* sglL */ = function(_/* EXTERNAL */, _1pz/* sglN */){
            var _1pA/* sglO */ = E(_1p7/* sgjM */);
            if(!_1pA/* sglO */._){
              return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), _1pz/* sglN */);});
            }else{
              var _1pB/* sglY */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h6/* FormEngine.FormElement.Rendering.lvl31 */, _1pz/* sglN */, _/* EXTERNAL */)),
              _1pC/* sgm4 */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1ew/* FormEngine.FormElement.Rendering.lvl16 */, new T(function(){
                return B(_12/* GHC.Base.++ */(_1je/* sfZe */, _1fQ/* FormEngine.FormElement.Identifiers.checkboxId1 */));
              },1), E(_1pB/* sglY */), _/* EXTERNAL */)),
              _1pD/* sgma */ = __app1/* EXTERNAL */(_1pf/* sgky */, E(_1pC/* sgm4 */)),
              _1pE/* sgme */ = __app1/* EXTERNAL */(_1ph/* sgkE */, _1pD/* sgma */),
              _1pF/* sgmi */ = function(_1pG/* sgmq */, _1pH/* sgmr */, _/* EXTERNAL */){
                while(1){
                  var _1pI/* sgmt */ = E(_1pG/* sgmq */);
                  if(!_1pI/* sgmt */._){
                    return _1pH/* sgmr */;
                  }else{
                    var _1pJ/* sgmw */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1pI/* sgmt */.a, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1pH/* sgmr */, _/* EXTERNAL */));
                    _1pG/* sgmq */ = _1pI/* sgmt */.b;
                    _1pH/* sgmr */ = _1pJ/* sgmw */;
                    continue;
                  }
                }
              },
              _1pK/* sgmA */ = B((function(_1pL/* sgmj */, _1pM/* sgmk */, _1pN/* sgml */, _/* EXTERNAL */){
                var _1pO/* sgmn */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1pL/* sgmj */, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1pN/* sgml */, _/* EXTERNAL */));
                return new F(function(){return _1pF/* sgmi */(_1pM/* sgmk */, _1pO/* sgmn */, _/* EXTERNAL */);});
              })(_1pA/* sglO */.a, _1pA/* sglO */.b, _1pE/* sgme */, _/* EXTERNAL */)),
              _1pP/* sgmF */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
              _1pQ/* sgmI */ = __app1/* EXTERNAL */(_1pP/* sgmF */, E(_1pK/* sgmA */));
              return new F(function(){return __app1/* EXTERNAL */(_1pP/* sgmF */, _1pQ/* sgmI */);});
            }
          },
          _1pR/* sgmQ */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1p6/* sgjK */)).e);
          if(!_1pR/* sgmQ */._){
            return new F(function(){return _1py/* sglL */(_/* EXTERNAL */, _1px/* sglA */);});
          }else{
            var _1pS/* sgmS */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dJ/* FormEngine.FormElement.Rendering.lvl3 */, _1px/* sglA */, _/* EXTERNAL */)),
            _1pT/* sgmX */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1pR/* sgmQ */.a, E(_1pS/* sgmS */), _/* EXTERNAL */));
            return new F(function(){return _1py/* sglL */(_/* EXTERNAL */, E(_1pT/* sgmX */));});
          }
        };
        if(!E(_1p7/* sgjM */)._){
          var _1pU/* sgn5 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1pv/* sglv */), _/* EXTERNAL */));
          return new F(function(){return _1pw/* sgly */(_/* EXTERNAL */, E(_1pU/* sgn5 */));});
        }else{
          var _1pV/* sgne */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h7/* FormEngine.FormElement.Rendering.lvl32 */, E(_1pv/* sglv */), _/* EXTERNAL */));
          return new F(function(){return _1pw/* sgly */(_/* EXTERNAL */, E(_1pV/* sgne */));});
        }
      };
      if(!E(_1jf/* sfZf */.b)){
        return new F(function(){return _1pl/* sgkS */(_/* EXTERNAL */, E(_1pk/* sgkP */));});
      }else{
        var _1pW/* sgno */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h9/* FormEngine.FormElement.Rendering.lvl34 */, _1h9/* FormEngine.FormElement.Rendering.lvl34 */, E(_1pk/* sgkP */), _/* EXTERNAL */));
        return new F(function(){return _1pl/* sgkS */(_/* EXTERNAL */, E(_1pW/* sgno */));});
      }
      break;
    case 10:
      var _1pX/* sgnt */ = _1jf/* sfZf */.a,
      _1pY/* sgnu */ = _1jf/* sfZf */.b,
      _1pZ/* sgnz */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h3/* FormEngine.FormElement.Rendering.lvl28 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1q0/* sgnE */ = B(_1cU/* FormEngine.JQuery.$wa1 */(_1h2/* FormEngine.FormElement.Rendering.lvl27 */, E(_1pZ/* sgnz */), _/* EXTERNAL */)),
      _1q1/* sgnJ */ = new T(function(){
        var _1q2/* sgnK */ = E(_1pX/* sgnt */);
        switch(_1q2/* sgnK */._){
          case 8:
            return E(_1q2/* sgnK */.b);
            break;
          case 9:
            return E(_1q2/* sgnK */.b);
            break;
          case 10:
            return E(_1q2/* sgnK */.b);
            break;
          default:
            return E(_5U/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _1q3/* sgnV */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1h1/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_4A/* GHC.Show.$fShowInt_$cshow */(_1q1/* sgnJ */));
      },1), E(_1q0/* sgnE */), _/* EXTERNAL */)),
      _1q4/* sgo0 */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1q5/* sgo3 */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1q3/* sgnV */)),
      _1q6/* sgo6 */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1q7/* sgo9 */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1q5/* sgo3 */),
      _1q8/* sgoc */ = B(_4r/* FormEngine.FormItem.fiDescriptor */(_1pX/* sgnt */)),
      _1q9/* sgon */ = B(_1fp/* FormEngine.FormElement.Rendering.a2 */(_1q8/* sgoc */.a, _1q1/* sgnJ */, _1q7/* sgo9 */, _/* EXTERNAL */)),
      _1qa/* sgoq */ = function(_/* EXTERNAL */, _1qb/* sgos */){
        var _1qc/* sgot */ = new T(function(){
          return E(E(_1j9/* sfZ7 */).e);
        }),
        _1qd/* sgoA */ = function(_1qe/* sgoB */, _1qf/* sgoC */, _/* EXTERNAL */){
          while(1){
            var _1qg/* sgoE */ = E(_1qe/* sgoB */);
            if(!_1qg/* sgoE */._){
              return _1qf/* sgoC */;
            }else{
              var _1qh/* sgoH */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1qg/* sgoE */.a, _1j9/* sfZ7 */, _1ja/* sfZ8 */, _1qf/* sgoC */, _/* EXTERNAL */));
              _1qe/* sgoB */ = _1qg/* sgoE */.b;
              _1qf/* sgoC */ = _1qh/* sgoH */;
              continue;
            }
          }
        },
        _1qi/* sgoK */ = function(_1qj/* sgoL */, _1qk/* sgoM */, _/* EXTERNAL */){
          var _1ql/* sgoO */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1eq/* FormEngine.FormElement.Rendering.lvl10 */, _1qk/* sgoM */, _/* EXTERNAL */)),
          _1qm/* sgoU */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1ql/* sgoO */)),
          _1qn/* sgoY */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qm/* sgoU */),
          _1qo/* sgp1 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1er/* FormEngine.FormElement.Rendering.lvl11 */, _1qn/* sgoY */, _/* EXTERNAL */)),
          _1qp/* sgp7 */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1qo/* sgp1 */)),
          _1qq/* sgpb */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qp/* sgp7 */),
          _1qr/* sgpe */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1es/* FormEngine.FormElement.Rendering.lvl12 */, _1qq/* sgpb */, _/* EXTERNAL */)),
          _1qs/* sgpk */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1qr/* sgpe */)),
          _1qt/* sgpo */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qs/* sgpk */),
          _1qu/* sgpr */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1et/* FormEngine.FormElement.Rendering.lvl13 */, _1qt/* sgpo */, _/* EXTERNAL */)),
          _1qv/* sgpx */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1qu/* sgpr */)),
          _1qw/* sgpB */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qv/* sgpx */),
          _1qx/* sgpE */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h5/* FormEngine.FormElement.Rendering.lvl30 */, _1qw/* sgpB */, _/* EXTERNAL */)),
          _1qy/* sgpK */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1qx/* sgpE */)),
          _1qz/* sgpO */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qy/* sgpK */),
          _1qA/* sgpT */ = B(_1qd/* sgoA */(B(_1bZ/* FormEngine.FormElement.FormElement.egElements */(_1qj/* sgoL */)), _1qz/* sgpO */, _/* EXTERNAL */)),
          _1qB/* sgpY */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
          _1qC/* sgq1 */ = __app1/* EXTERNAL */(_1qB/* sgpY */, E(_1qA/* sgpT */)),
          _1qD/* sgq5 */ = __app1/* EXTERNAL */(_1qB/* sgpY */, _1qC/* sgq1 */),
          _1qE/* sgqd */ = function(_/* EXTERNAL */, _1qF/* sgqf */){
            var _1qG/* sgqh */ = __app1/* EXTERNAL */(_1qB/* sgpY */, _1qF/* sgqf */),
            _1qH/* sgql */ = __app1/* EXTERNAL */(_1qB/* sgpY */, _1qG/* sgqh */);
            return new F(function(){return __app1/* EXTERNAL */(_1qB/* sgpY */, _1qH/* sgql */);});
          };
          if(E(E(_1qj/* sgoL */).b)<=0){
            return new F(function(){return _1qE/* sgqd */(_/* EXTERNAL */, _1qD/* sgq5 */);});
          }else{
            var _1qI/* sgqv */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1h4/* FormEngine.FormElement.Rendering.lvl29 */, _1qD/* sgq5 */, _/* EXTERNAL */)),
            _1qJ/* sgqB */ = __app1/* EXTERNAL */(_1q4/* sgo0 */, E(_1qI/* sgqv */)),
            _1qK/* sgqF */ = __app1/* EXTERNAL */(_1q6/* sgo6 */, _1qJ/* sgqB */),
            _1qL/* sgqI */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1qc/* sgot */, _1qK/* sgqF */, _/* EXTERNAL */)),
            _1qM/* sgqN */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1fF/* FormEngine.FormElement.Rendering.a6 */, E(_1qL/* sgqI */), _/* EXTERNAL */)),
            _1qN/* sgqT */ = __app1/* EXTERNAL */(_1qB/* sgpY */, E(_1qM/* sgqN */));
            return new F(function(){return _1qE/* sgqd */(_/* EXTERNAL */, _1qN/* sgqT */);});
          }
        },
        _1qO/* sgqW */ = function(_1qP/* sgqX */, _1qQ/* sgqY */, _/* EXTERNAL */){
          while(1){
            var _1qR/* sgr0 */ = E(_1qP/* sgqX */);
            if(!_1qR/* sgr0 */._){
              return _1qQ/* sgqY */;
            }else{
              var _1qS/* sgr5 */ = B(_1qi/* sgoK */(_1qR/* sgr0 */.a, E(_1qQ/* sgqY */), _/* EXTERNAL */));
              _1qP/* sgqX */ = _1qR/* sgr0 */.b;
              _1qQ/* sgqY */ = _1qS/* sgr5 */;
              continue;
            }
          }
        },
        _1qT/* sgr8 */ = B(_1qO/* sgqW */(_1pY/* sgnu */, _1qb/* sgos */, _/* EXTERNAL */)),
        _1qU/* sgre */ = B(_Ig/* FormEngine.JQuery.$wa3 */(B(_1fL/* FormEngine.FormContext.addImg */(_1j9/* sfZ7 */)), E(_1qT/* sgr8 */), _/* EXTERNAL */)),
        _1qV/* sgrj */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gZ/* FormEngine.FormElement.Rendering.lvl24 */, _1h0/* FormEngine.FormElement.Rendering.lvl25 */, E(_1qU/* sgre */), _/* EXTERNAL */)),
        _1qW/* sgro */ = new T(function(){
          var _1qX/* sgrp */ = function(_1qY/* sgrq */, _1qZ/* sgrr */){
            while(1){
              var _1r0/* sgrs */ = E(_1qY/* sgrq */);
              if(!_1r0/* sgrs */._){
                return E(_1qZ/* sgrr */);
              }else{
                _1qY/* sgrq */ = _1r0/* sgrs */.b;
                _1qZ/* sgrr */ = _1r0/* sgrs */.a;
                continue;
              }
            }
          };
          return B(_1qX/* sgrp */(_1pY/* sgnu */, _1ge/* GHC.List.last1 */));
        }),
        _1r1/* sgsx */ = function(_1r2/* sgrv */, _/* EXTERNAL */){
          var _1r3/* sgrC */ = __app1/* EXTERNAL */(E(_1fv/* FormEngine.JQuery.target_f1 */), E(_1r2/* sgrv */)),
          _1r4/* sgrF */ = B(_1d2/* FormEngine.JQuery.$wa10 */(_1gZ/* FormEngine.FormElement.Rendering.lvl24 */, _1r3/* sgrC */, _/* EXTERNAL */)),
          _1r5/* sgrK */ = B(_Pr/* Text.Read.readEither6 */(B(_Py/* Text.ParserCombinators.ReadP.run */(_1gU/* FormEngine.FormElement.Rendering.lvl2 */, new T(function(){
            return B(_7/* GHC.HastePrim.fromJSStr */(_1r4/* sgrF */));
          })))));
          if(!_1r5/* sgrK */._){
            return E(_1gh/* FormEngine.FormElement.Rendering.lvl */);
          }else{
            if(!E(_1r5/* sgrK */.b)._){
              var _1r6/* sgrP */ = E(_1r5/* sgrK */.a),
              _1r7/* sgrT */ = B(_HT/* FormEngine.JQuery.$wa6 */(_1gZ/* FormEngine.FormElement.Rendering.lvl24 */, B(_4e/* GHC.Show.$wshowSignedInt */(0, _1r6/* sgrP */+1|0, _I/* GHC.Types.[] */)), _1r3/* sgrC */, _/* EXTERNAL */)),
              _1r8/* sgrZ */ = __app1/* EXTERNAL */(E(_1i5/* FormEngine.JQuery.prev_f1 */), _1r3/* sgrC */),
              _1r9/* sgs2 */ = new T(function(){
                return new T2(0,_1ra/* sgs3 */,_1r6/* sgrP */);
              }),
              _1ra/* sgs3 */ = new T(function(){
                return B(_2S/* GHC.Base.map */(function(_1rb/* B1 */){
                  return new F(function(){return _1iC/* FormEngine.FormElement.FormElement.setGroupOfElem */(new T1(1,_1r9/* sgs2 */), _1rb/* B1 */);});
                }, E(_1qW/* sgro */).a));
              }),
              _1rc/* sgs9 */ = B(_1qi/* sgoK */(_1r9/* sgs2 */, _1r8/* sgrZ */, _/* EXTERNAL */)),
              _1rd/* sgsc */ = function(_1re/* sgsd */, _/* EXTERNAL */){
                while(1){
                  var _1rf/* sgsf */ = E(_1re/* sgsd */);
                  if(!_1rf/* sgsf */._){
                    return _0/* GHC.Tuple.() */;
                  }else{
                    var _1rg/* sgsj */ = B(_PJ/* FormEngine.JQuery.selectByName1 */(B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1rf/* sgsf */.a)), _/* EXTERNAL */)),
                    _1rh/* sgso */ = B(_KX/* FormEngine.JQuery.$wa14 */(E(_1rg/* sgsj */), _/* EXTERNAL */));
                    _1re/* sgsd */ = _1rf/* sgsf */.b;
                    continue;
                  }
                }
              },
              _1ri/* sgsr */ = B(_1rd/* sgsc */(_1ra/* sgs3 */, _/* EXTERNAL */));
              return _0/* GHC.Tuple.() */;
            }else{
              return E(_1gj/* FormEngine.FormElement.Rendering.lvl1 */);
            }
          }
        },
        _1rj/* sgsy */ = B(_1d7/* FormEngine.JQuery.$wa23 */(_1r1/* sgsx */, E(_1qV/* sgrj */), _/* EXTERNAL */));
        return new F(function(){return __app1/* EXTERNAL */(E(_HY/* FormEngine.JQuery.addClassInside_f1 */), E(_1rj/* sgsy */));});
      },
      _1rk/* sgsK */ = E(_1q8/* sgoc */.e);
      if(!_1rk/* sgsK */._){
        return new F(function(){return _1qa/* sgoq */(_/* EXTERNAL */, _1q9/* sgon */);});
      }else{
        var _1rl/* sgsO */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1dJ/* FormEngine.FormElement.Rendering.lvl3 */, E(_1q9/* sgon */), _/* EXTERNAL */)),
        _1rm/* sgsT */ = B(_Il/* FormEngine.JQuery.$wa34 */(_1rk/* sgsK */.a, E(_1rl/* sgsO */), _/* EXTERNAL */));
        return new F(function(){return _1qa/* sgoq */(_/* EXTERNAL */, _1rm/* sgsT */);});
      }
      break;
    case 11:
      var _1rn/* sgt0 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gW/* FormEngine.FormElement.Rendering.lvl21 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1ro/* sgt5 */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1rp/* sgt8 */ = __app1/* EXTERNAL */(_1ro/* sgt5 */, E(_1rn/* sgt0 */)),
      _1rq/* sgtb */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1rr/* sgte */ = __app1/* EXTERNAL */(_1rq/* sgtb */, _1rp/* sgt8 */),
      _1rs/* sgth */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1er/* FormEngine.FormElement.Rendering.lvl11 */, _1rr/* sgte */, _/* EXTERNAL */)),
      _1rt/* sgtn */ = __app1/* EXTERNAL */(_1ro/* sgt5 */, E(_1rs/* sgth */)),
      _1ru/* sgtr */ = __app1/* EXTERNAL */(_1rq/* sgtb */, _1rt/* sgtn */),
      _1rv/* sgtu */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1es/* FormEngine.FormElement.Rendering.lvl12 */, _1ru/* sgtr */, _/* EXTERNAL */)),
      _1rw/* sgtA */ = __app1/* EXTERNAL */(_1ro/* sgt5 */, E(_1rv/* sgtu */)),
      _1rx/* sgtE */ = __app1/* EXTERNAL */(_1rq/* sgtb */, _1rw/* sgtA */),
      _1ry/* sgtH */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gV/* FormEngine.FormElement.Rendering.lvl20 */, _1rx/* sgtE */, _/* EXTERNAL */)),
      _1rz/* sgtN */ = __app1/* EXTERNAL */(_1ro/* sgt5 */, E(_1ry/* sgtH */)),
      _1rA/* sgtR */ = __app1/* EXTERNAL */(_1rq/* sgtb */, _1rz/* sgtN */),
      _1rB/* sgtU */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gY/* FormEngine.FormElement.Rendering.lvl23 */, _1rA/* sgtR */, _/* EXTERNAL */)),
      _1rC/* sguc */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, new T(function(){
        var _1rD/* sgu9 */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).a);
        if(!_1rD/* sgu9 */._){
          return E(_1gX/* FormEngine.FormElement.Rendering.lvl22 */);
        }else{
          return E(_1rD/* sgu9 */.a);
        }
      },1), E(_1rB/* sgtU */), _/* EXTERNAL */)),
      _1rE/* sguh */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
      _1rF/* sguk */ = __app1/* EXTERNAL */(_1rE/* sguh */, E(_1rC/* sguc */)),
      _1rG/* sguo */ = __app1/* EXTERNAL */(_1rE/* sguh */, _1rF/* sguk */),
      _1rH/* sgus */ = __app1/* EXTERNAL */(_1rE/* sguh */, _1rG/* sguo */),
      _1rI/* sguw */ = __app1/* EXTERNAL */(_1rE/* sguh */, _1rH/* sgus */);
      return new F(function(){return _1dN/* FormEngine.FormElement.Rendering.a1 */(_1jf/* sfZf */, _1rI/* sguw */, _/* EXTERNAL */);});
      break;
    default:
      var _1rJ/* sguE */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gW/* FormEngine.FormElement.Rendering.lvl21 */, E(_1jb/* sfZ9 */), _/* EXTERNAL */)),
      _1rK/* sguJ */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1rL/* sguM */ = __app1/* EXTERNAL */(_1rK/* sguJ */, E(_1rJ/* sguE */)),
      _1rM/* sguP */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1rN/* sguS */ = __app1/* EXTERNAL */(_1rM/* sguP */, _1rL/* sguM */),
      _1rO/* sguV */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1er/* FormEngine.FormElement.Rendering.lvl11 */, _1rN/* sguS */, _/* EXTERNAL */)),
      _1rP/* sgv1 */ = __app1/* EXTERNAL */(_1rK/* sguJ */, E(_1rO/* sguV */)),
      _1rQ/* sgv5 */ = __app1/* EXTERNAL */(_1rM/* sguP */, _1rP/* sgv1 */),
      _1rR/* sgv8 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1es/* FormEngine.FormElement.Rendering.lvl12 */, _1rQ/* sgv5 */, _/* EXTERNAL */)),
      _1rS/* sgve */ = __app1/* EXTERNAL */(_1rK/* sguJ */, E(_1rR/* sgv8 */)),
      _1rT/* sgvi */ = __app1/* EXTERNAL */(_1rM/* sguP */, _1rS/* sgve */),
      _1rU/* sgvl */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gV/* FormEngine.FormElement.Rendering.lvl20 */, _1rT/* sgvi */, _/* EXTERNAL */)),
      _1rV/* sgvr */ = __app1/* EXTERNAL */(_1rK/* sguJ */, E(_1rU/* sgvl */)),
      _1rW/* sgvv */ = __app1/* EXTERNAL */(_1rM/* sguP */, _1rV/* sgvr */),
      _1rX/* sgvy */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1gm/* FormEngine.FormElement.Rendering.lvl19 */, _1rW/* sgvv */, _/* EXTERNAL */)),
      _1rY/* sgvQ */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1gl/* FormEngine.FormElement.Rendering.lvl18 */, new T(function(){
        var _1rZ/* sgvN */ = E(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1jf/* sfZf */.a)).a);
        if(!_1rZ/* sgvN */._){
          return E(_1gk/* FormEngine.FormElement.Rendering.lvl17 */);
        }else{
          return E(_1rZ/* sgvN */.a);
        }
      },1), E(_1rX/* sgvy */), _/* EXTERNAL */)),
      _1s0/* sgvV */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
      _1s1/* sgvY */ = __app1/* EXTERNAL */(_1s0/* sgvV */, E(_1rY/* sgvQ */)),
      _1s2/* sgw2 */ = __app1/* EXTERNAL */(_1s0/* sgvV */, _1s1/* sgvY */),
      _1s3/* sgw6 */ = __app1/* EXTERNAL */(_1s0/* sgvV */, _1s2/* sgw2 */),
      _1s4/* sgwa */ = __app1/* EXTERNAL */(_1s0/* sgvV */, _1s3/* sgw6 */);
      return new F(function(){return _1dN/* FormEngine.FormElement.Rendering.a1 */(_1jf/* sfZf */, _1s4/* sgwa */, _/* EXTERNAL */);});
  }
},
_1s5/* foldElements1 */ = function(_1s6/* sgwe */, _1s7/* sgwf */, _1s8/* sgwg */, _1s9/* sgwh */, _/* EXTERNAL */){
  var _1sa/* sgwj */ = function(_1sb/* sgwk */, _1sc/* sgwl */, _/* EXTERNAL */){
    while(1){
      var _1sd/* sgwn */ = E(_1sb/* sgwk */);
      if(!_1sd/* sgwn */._){
        return _1sc/* sgwl */;
      }else{
        var _1se/* sgwq */ = B(_1j7/* FormEngine.FormElement.Rendering.foldElements2 */(_1sd/* sgwn */.a, _1s7/* sgwf */, _1s8/* sgwg */, _1sc/* sgwl */, _/* EXTERNAL */));
        _1sb/* sgwk */ = _1sd/* sgwn */.b;
        _1sc/* sgwl */ = _1se/* sgwq */;
        continue;
      }
    }
  };
  return new F(function(){return _1sa/* sgwj */(_1s6/* sgwe */, _1s9/* sgwh */, _/* EXTERNAL */);});
},
_1sf/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("textarea"));
}),
_1sg/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("select"));
}),
_1sh/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/add.png\'/>"));
}),
_1si/* baseURL */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/"));
}),
_1sj/* staticURL1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("static/"));
}),
_1sk/* staticURL */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1si/* Config.Config.baseURL */, _1sj/* Config.Config.staticURL1 */));
}),
_1sl/* lvl11 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1sk/* Config.Config.staticURL */, _1sh/* Form.lvl10 */));
}),
_1sm/* lvl12 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'add\' class=\'button-add\' src=\'", _1sl/* Form.lvl11 */));
}),
_1sn/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("img/remove.png\'/>"));
}),
_1so/* lvl14 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1sk/* Config.Config.staticURL */, _1sn/* Form.lvl13 */));
}),
_1sp/* lvl15 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img alt=\'remove\' class=\'button-add\' src=\'", _1so/* Form.lvl14 */));
}),
_1sq/* selectSVG2 */ = "(function (selector, jq) { if (jq[0].contentDocument !== null) { var res = $(selector, jq[0].contentDocument.documentElement); if (res.length === 0) { console.warn(\'empty $ selection \' + selector); }; return res; } else return jq; })",
_1sr/* $wa19 */ = function(_1ss/* stRG */, _1st/* stRH */, _/* EXTERNAL */){
  var _1su/* stRR */ = eval/* EXTERNAL */(E(_1sq/* FormEngine.JQuery.selectSVG2 */));
  return new F(function(){return __app2/* EXTERNAL */(E(_1su/* stRR */), toJSStr/* EXTERNAL */(E(_1ss/* stRG */)), _1st/* stRH */);});
},
_1sv/* highlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#FBB48F"));
}),
_1sw/* tinkerDiagSvgConsumer6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("fill"));
}),
_1sx/* tinkerDiagSvgConsumer7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1sy/* tinkerDiagSvgConsumer5 */ = function(_1sz/* seOO */, _1sA/* seOP */, _/* EXTERNAL */){
  var _1sB/* seOS */ = B(_56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1sx/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1sA/* seOP */)), _/* EXTERNAL */)),
  _1sC/* seOY */ = B(_1sr/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1sx/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1sz/* seOO */)), E(_1sB/* seOS */), _/* EXTERNAL */)),
  _1sD/* seP3 */ = B(_43/* FormEngine.JQuery.$wa2 */(_1sw/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1sv/* DiagramDecorator.highlightCol */, E(_1sC/* seOY */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1sE/* $wa */ = function(_1sF/* seQM */, _/* EXTERNAL */){
  var _1sG/* seQZ */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_LH/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
      return B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_1sF/* seQM */))));
    },1)));
  }),
  _1sH/* seR2 */ = function(_1sI/* seR3 */, _/* EXTERNAL */){
    while(1){
      var _1sJ/* seR5 */ = E(_1sI/* seR3 */);
      if(!_1sJ/* seR5 */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1sK/* seR8 */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sJ/* seR5 */.a, _1sG/* seQZ */, _/* EXTERNAL */));
        _1sI/* seR3 */ = _1sJ/* seR5 */.b;
        continue;
      }
    }
  },
  _1sL/* seRb */ = B(_1sH/* seR2 */(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1sF/* seQM */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1sM/* tinkerDiagramForElement1 */ = function(_1sN/* seRe */, _1sO/* seRf */, _/* EXTERNAL */){
  return new F(function(){return _1sE/* DiagramDecorator.$wa */(_1sN/* seRe */, _/* EXTERNAL */);});
},
_1sP/* lvl16 */ = new T1(1,_1sM/* DiagramDecorator.tinkerDiagramForElement1 */),
_1sQ/* lowlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("white"));
}),
_1sR/* $wa1 */ = function(_1sS/* seO7 */, _/* EXTERNAL */){
  var _1sT/* seOk */ = new T(function(){
    var _1sU/* seOn */ = new T(function(){
      return B(_12/* GHC.Base.++ */(_LH/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
        return B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_1sS/* seO7 */))));
      },1)));
    },1);
    return B(_12/* GHC.Base.++ */(_1sx/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1sU/* seOn */));
  }),
  _1sV/* seOo */ = function(_1sW/* seOp */, _/* EXTERNAL */){
    while(1){
      var _1sX/* seOr */ = E(_1sW/* seOp */);
      if(!_1sX/* seOr */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1sY/* seOu */ = B(_56/* FormEngine.JQuery.select1 */(_1sT/* seOk */, _/* EXTERNAL */)),
        _1sZ/* seOA */ = B(_1sr/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1sx/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1sX/* seOr */.a)), E(_1sY/* seOu */), _/* EXTERNAL */)),
        _1t0/* seOF */ = B(_43/* FormEngine.JQuery.$wa2 */(_1sw/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1sQ/* DiagramDecorator.lowlightCol */, E(_1sZ/* seOA */), _/* EXTERNAL */));
        _1sW/* seOp */ = _1sX/* seOr */.b;
        continue;
      }
    }
  },
  _1t1/* seOI */ = B(_1sV/* seOo */(B(_4r/* FormEngine.FormItem.fiDescriptor */(B(_4u/* FormEngine.FormElement.FormElement.formItem */(_1sS/* seO7 */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1t2/* tinkerDiagramForElementBlur1 */ = function(_1t3/* seOL */, _1t4/* seOM */, _/* EXTERNAL */){
  return new F(function(){return _1sR/* DiagramDecorator.$wa1 */(_1t3/* seOL */, _/* EXTERNAL */);});
},
_1t5/* lvl17 */ = new T1(1,_1t2/* DiagramDecorator.tinkerDiagramForElementBlur1 */),
_1t6/* lvl18 */ = new T3(0,_1sP/* Form.lvl16 */,_1t5/* Form.lvl17 */,_2o/* GHC.Base.Nothing */),
_1t7/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'desc-subpane\'>"));
}),
_1t8/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'main-pane\'></div>"));
}),
_1t9/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1ta/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<object class=\'svg-help\' href=\'http://caniuse.com/#feat=svg\' data=\'/static/img/data_process.svg\' type=\'image/svg+xml\'><br>"));
}),
_1tb/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\'long-desc\'>"));
}),
_1tc/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/hint-icon.png\' style=\'margin-right: 5px;\'>"));
}),
_1td/* lvl24 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1sk/* Config.Config.staticURL */, _1tc/* Form.lvl23 */));
}),
_1te/* lvl25 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img src=\'", _1td/* Form.lvl24 */));
}),
_1tf/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span/>"));
}),
_1tg/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#m_questionnaire_form"));
}),
_1th/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input"));
}),
_1ti/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input:checked"));
}),
_1tj/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'form-subpane\'>"));
}),
_1tk/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/valid.png\'/>"));
}),
_1tl/* lvl5 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1sk/* Config.Config.staticURL */, _1tk/* Form.lvl4 */));
}),
_1tm/* lvl6 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1tl/* Form.lvl5 */));
}),
_1tn/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/invalid.png\'/>"));
}),
_1to/* lvl8 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1sk/* Config.Config.staticURL */, _1tn/* Form.lvl7 */));
}),
_1tp/* lvl9 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1to/* Form.lvl8 */));
}),
_1tq/* click1 */ = function(_1tr/* stAO */, _/* EXTERNAL */){
  return new F(function(){return _Ln/* FormEngine.JQuery.$wa5 */(E(_1tr/* stAO */), _/* EXTERNAL */);});
},
_1ts/* selectTab1 */ = function(_1tt/* sdnh */, _1tu/* sdni */, _/* EXTERNAL */){
  var _1tv/* sdno */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_IQ/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
      return B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_71/* GHC.List.$w!! */(_1tu/* sdni */, E(_1tt/* sdnh */)))));
    },1)));
  },1),
  _1tw/* sdnq */ = B(_56/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J5/* FormEngine.FormElement.Tabs.colorizeTabs5 */, _1tv/* sdno */)), _/* EXTERNAL */));
  return new F(function(){return _1tq/* FormEngine.JQuery.click1 */(_1tw/* sdnq */, _/* EXTERNAL */);});
},
_1tx/* tinkerDiagSvgConsumer4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_1ty/* tinkerDiagSvgCurator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_1tz/* tinkerDiagSvgCurator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_1tA/* tinkerDiagSvgCurator5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_1tB/* tinkerDiagSvgCurator6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_1tC/* tinkerDiagSvgCurator8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_1tD/* tinkerDiagSvgInvestigator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution_box"));
}),
_1tE/* tinkerDiagSvgManager4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_1tF/* tinkerDiagramForChapterElement1 */ = function(_1tG/* seRh */, _/* EXTERNAL */){
  var _1tH/* seRj */ = B(_4V/* FormEngine.FormElement.FormElement.elementId */(_1tG/* seRh */));
  if(!_1tH/* seRj */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _1tI/* seRl */ = _1tH/* seRj */.b;
    switch(E(_1tH/* seRj */.a)){
      case 48:
        if(!E(_1tI/* seRl */)._){
          var _1tJ/* seRr */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tD/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 49:
        if(!E(_1tI/* seRl */)._){
          var _1tK/* seRy */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tE/* DiagramDecorator.tinkerDiagSvgManager4 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 50:
        if(!E(_1tI/* seRl */)._){
          var _1tL/* seRF */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 51:
        if(!E(_1tI/* seRl */)._){
          var _1tM/* seRM */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tx/* DiagramDecorator.tinkerDiagSvgConsumer4 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 52:
        if(!E(_1tI/* seRl */)._){
          var _1tN/* seRT */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 53:
        if(!E(_1tI/* seRl */)._){
          var _1tO/* seRZ */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_LH/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
              return B(_4V/* FormEngine.FormElement.FormElement.elementId */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_1tG/* seRh */))));
            },1)));
          }),
          _1tP/* seS2 */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tA/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1tO/* seRZ */, _/* EXTERNAL */)),
          _1tQ/* seS5 */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tz/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1tO/* seRZ */, _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 54:
        if(!E(_1tI/* seRl */)._){
          var _1tR/* seSc */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ty/* DiagramDecorator.tinkerDiagSvgCurator3 */, new T(function(){
            return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tG/* seRh */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 55:
        var _1tS/* seSh */ = E(_1tI/* seRl */);
        return _0/* GHC.Tuple.() */;
      default:
        return _0/* GHC.Tuple.() */;
    }
  }
},
_1tT/* generateQuestionnaire1 */ = function(_1tU/* sljo */, _/* EXTERNAL */){
  var _1tV/* sljq */ = B(_56/* FormEngine.JQuery.select1 */(_1tg/* Form.lvl27 */, _/* EXTERNAL */)),
  _1tW/* sljv */ = new T2(1,_Lz/* Form.aboutTab */,_1tU/* sljo */),
  _1tX/* slln */ = new T(function(){
    var _1tY/* sllm */ = function(_1tZ/* sljx */, _/* EXTERNAL */){
      var _1u0/* sljz */ = B(_56/* FormEngine.JQuery.select1 */(_1t8/* Form.lvl2 */, _/* EXTERNAL */)),
      _1u1/* sljE */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1tj/* Form.lvl3 */, E(_1u0/* sljz */), _/* EXTERNAL */)),
      _1u2/* sljJ */ = E(_I0/* FormEngine.JQuery.addClassInside_f3 */),
      _1u3/* sljM */ = __app1/* EXTERNAL */(_1u2/* sljJ */, E(_1u1/* sljE */)),
      _1u4/* sljP */ = E(_HZ/* FormEngine.JQuery.addClassInside_f2 */),
      _1u5/* sljS */ = __app1/* EXTERNAL */(_1u4/* sljP */, _1u3/* sljM */),
      _1u6/* sljX */ = B(_1s5/* FormEngine.FormElement.Rendering.foldElements1 */(B(_HK/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_1tZ/* sljx */)), new T5(0,_1tU/* sljo */,_1tm/* Form.lvl6 */,_1tp/* Form.lvl9 */,_1sm/* Form.lvl12 */,_1sp/* Form.lvl15 */), _1t6/* Form.lvl18 */, _1u5/* sljS */, _/* EXTERNAL */)),
      _1u7/* slk2 */ = E(_HY/* FormEngine.JQuery.addClassInside_f1 */),
      _1u8/* slk5 */ = __app1/* EXTERNAL */(_1u7/* slk2 */, E(_1u6/* sljX */)),
      _1u9/* slk8 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1t7/* Form.lvl19 */, _1u8/* slk5 */, _/* EXTERNAL */)),
      _1ua/* slke */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1t9/* Form.lvl20 */, new T(function(){
        return B(_LC/* FormEngine.FormElement.Identifiers.descSubpaneId */(_1tZ/* sljx */));
      },1), E(_1u9/* slk8 */), _/* EXTERNAL */)),
      _1ub/* slkk */ = __app1/* EXTERNAL */(_1u2/* sljJ */, E(_1ua/* slke */)),
      _1uc/* slko */ = __app1/* EXTERNAL */(_1u4/* sljP */, _1ub/* slkk */),
      _1ud/* slkr */ = B(_L2/* FormEngine.JQuery.$wa26 */(_1ta/* Form.lvl21 */, _1uc/* slko */, _/* EXTERNAL */)),
      _1ue/* slkx */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1t9/* Form.lvl20 */, new T(function(){
        return B(_LI/* FormEngine.FormElement.Identifiers.diagramId */(_1tZ/* sljx */));
      },1), E(_1ud/* slkr */), _/* EXTERNAL */)),
      _1uf/* slkF */ = B(_Lg/* FormEngine.JQuery.$wa29 */(function(_1ug/* slkC */, _/* EXTERNAL */){
        return new F(function(){return _1tF/* DiagramDecorator.tinkerDiagramForChapterElement1 */(_1tZ/* sljx */, _/* EXTERNAL */);});
      }, E(_1ue/* slkx */), _/* EXTERNAL */)),
      _1uh/* slkK */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1tb/* Form.lvl22 */, E(_1uf/* slkF */), _/* EXTERNAL */)),
      _1ui/* slkQ */ = B(_I1/* FormEngine.JQuery.$wa20 */(_1t9/* Form.lvl20 */, new T(function(){
        return B(_LF/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_1tZ/* sljx */));
      },1), E(_1uh/* slkK */), _/* EXTERNAL */)),
      _1uj/* slkW */ = __app1/* EXTERNAL */(_1u2/* sljJ */, E(_1ui/* slkQ */)),
      _1uk/* sll0 */ = __app1/* EXTERNAL */(_1u4/* sljP */, _1uj/* slkW */),
      _1ul/* sll3 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1te/* Form.lvl25 */, _1uk/* sll0 */, _/* EXTERNAL */)),
      _1um/* sll8 */ = B(_Ig/* FormEngine.JQuery.$wa3 */(_1tf/* Form.lvl26 */, E(_1ul/* sll3 */), _/* EXTERNAL */)),
      _1un/* slle */ = __app1/* EXTERNAL */(_1u7/* slk2 */, E(_1um/* sll8 */));
      return new F(function(){return __app1/* EXTERNAL */(_1u7/* slk2 */, _1un/* slle */);});
    };
    return B(_2S/* GHC.Base.map */(_1tY/* sllm */, _1tU/* sljo */));
  }),
  _1uo/* sllp */ = B(_JO/* FormEngine.FormElement.Tabs.$wa */(_1tW/* sljv */, new T2(1,_LB/* Form.aboutTabPaneJq1 */,_1tX/* slln */), E(_1tV/* sljq */), _/* EXTERNAL */)),
  _1up/* slls */ = B(_1ts/* FormEngine.FormElement.Tabs.selectTab1 */(_Lr/* Form.aboutTab4 */, _1tW/* sljv */, _/* EXTERNAL */)),
  _1uq/* sllv */ = B(_56/* FormEngine.JQuery.select1 */(_1ti/* Form.lvl29 */, _/* EXTERNAL */)),
  _1ur/* sllA */ = B(_Ln/* FormEngine.JQuery.$wa5 */(E(_1uq/* sllv */), _/* EXTERNAL */)),
  _1us/* sllF */ = B(_Ln/* FormEngine.JQuery.$wa5 */(E(_1ur/* sllA */), _/* EXTERNAL */)),
  _1ut/* sllI */ = B(_56/* FormEngine.JQuery.select1 */(_1th/* Form.lvl28 */, _/* EXTERNAL */)),
  _1uu/* sllN */ = B(_KX/* FormEngine.JQuery.$wa14 */(E(_1ut/* sllI */), _/* EXTERNAL */)),
  _1uv/* sllQ */ = B(_56/* FormEngine.JQuery.select1 */(_1sf/* Form.lvl */, _/* EXTERNAL */)),
  _1uw/* sllV */ = B(_KX/* FormEngine.JQuery.$wa14 */(E(_1uv/* sllQ */), _/* EXTERNAL */)),
  _1ux/* sllY */ = B(_56/* FormEngine.JQuery.select1 */(_1sg/* Form.lvl1 */, _/* EXTERNAL */)),
  _1uy/* slm3 */ = B(_KX/* FormEngine.JQuery.$wa14 */(E(_1ux/* sllY */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1uz/* go */ = function(_1uA/* sqbI */){
  while(1){
    var _1uB/* sqbJ */ = E(_1uA/* sqbI */);
    if(!_1uB/* sqbJ */._){
      return false;
    }else{
      if(!E(_1uB/* sqbJ */.a)._){
        return true;
      }else{
        _1uA/* sqbI */ = _1uB/* sqbJ */.b;
        continue;
      }
    }
  }
},
_1uC/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Generate"));
}),
_1uD/* a2 */ = function(_1uE/* s1vnB */, _1uF/* s1vnC */){
  return new F(function(){return _1uG/* GHC.Read.$wa20 */(_1uF/* s1vnC */);});
},
_1uG/* $wa20 */ = function(_1uH/* s1vnD */){
  var _1uI/* s1vnI */ = new T(function(){
    return B(_128/* Text.Read.Lex.expect2 */(function(_1uJ/* s1vnF */){
      var _1uK/* s1vnG */ = E(_1uJ/* s1vnF */);
      if(!_1uK/* s1vnG */._){
        return new F(function(){return A1(_1uH/* s1vnD */,_1uK/* s1vnG */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1uL/* s1vnJ */ = function(_1uM/* s1vnK */){
    return E(_1uI/* s1vnI */);
  };
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1uN/* s1vnL */){
    return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1uN/* s1vnL */, _1uL/* s1vnJ */);});
  }), new T(function(){
    return new T1(1,B(_12G/* GHC.Read.$wa3 */(_1uD/* GHC.Read.a2 */, _1uH/* s1vnD */)));
  }));});
},
_1uO/* $fReadChar2 */ = function(_1uP/* s1vnR */, _1uQ/* s1vnS */){
  return new F(function(){return _1uG/* GHC.Read.$wa20 */(_1uQ/* s1vnS */);});
},
_1uR/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("["));
}),
_1uS/* $wa */ = function(_1uT/* s1vjF */, _1uU/* s1vjG */){
  var _1uV/* s1vjH */ = function(_1uW/* s1vjI */, _1uX/* s1vjJ */){
    var _1uY/* s1vjK */ = new T(function(){
      return B(A1(_1uX/* s1vjJ */,_I/* GHC.Types.[] */));
    }),
    _1uZ/* s1vjL */ = new T(function(){
      var _1v0/* s1vjQ */ = function(_1v1/* s1vjM */){
        return new F(function(){return _1uV/* s1vjH */(_8n/* GHC.Types.True */, function(_1v2/* s1vjN */){
          return new F(function(){return A1(_1uX/* s1vjJ */,new T2(1,_1v1/* s1vjM */,_1v2/* s1vjN */));});
        });});
      };
      return B(A2(_1uT/* s1vjF */,_12F/* Text.ParserCombinators.ReadPrec.minPrec */, _1v0/* s1vjQ */));
    }),
    _1v3/* s1vk8 */ = new T(function(){
      return B(_128/* Text.Read.Lex.expect2 */(function(_1v4/* s1vjS */){
        var _1v5/* s1vjT */ = E(_1v4/* s1vjS */);
        if(_1v5/* s1vjT */._==2){
          var _1v6/* s1vjV */ = E(_1v5/* s1vjT */.a);
          if(!_1v6/* s1vjV */._){
            return new T0(2);
          }else{
            var _1v7/* s1vjX */ = _1v6/* s1vjV */.b;
            switch(E(_1v6/* s1vjV */.a)){
              case 44:
                return (E(_1v7/* s1vjX */)._==0) ? (!E(_1uW/* s1vjI */)) ? new T0(2) : E(_1uZ/* s1vjL */) : new T0(2);
              case 93:
                return (E(_1v7/* s1vjX */)._==0) ? E(_1uY/* s1vjK */) : new T0(2);
              default:
                return new T0(2);
            }
          }
        }else{
          return new T0(2);
        }
      }));
    }),
    _1v8/* s1vk9 */ = function(_1v9/* s1vka */){
      return E(_1v3/* s1vk8 */);
    };
    return new T1(1,function(_1va/* s1vkb */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1va/* s1vkb */, _1v8/* s1vk9 */);});
    });
  },
  _1vb/* s1vkd */ = function(_1vc/* s1vkf */, _1vd/* s1vkg */){
    return new F(function(){return _1ve/* s1vke */(_1vd/* s1vkg */);});
  },
  _1ve/* s1vke */ = function(_1vf/* s1vkh */){
    var _1vg/* s1vki */ = new T(function(){
      var _1vh/* s1vkj */ = new T(function(){
        var _1vi/* s1vkq */ = new T(function(){
          var _1vj/* s1vkp */ = function(_1vk/* s1vkl */){
            return new F(function(){return _1uV/* s1vjH */(_8n/* GHC.Types.True */, function(_1vl/* s1vkm */){
              return new F(function(){return A1(_1vf/* s1vkh */,new T2(1,_1vk/* s1vkl */,_1vl/* s1vkm */));});
            });});
          };
          return B(A2(_1uT/* s1vjF */,_12F/* Text.ParserCombinators.ReadPrec.minPrec */, _1vj/* s1vkp */));
        });
        return B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_1uV/* s1vjH */(_2G/* GHC.Types.False */, _1vf/* s1vkh */)), _1vi/* s1vkq */));
      });
      return B(_128/* Text.Read.Lex.expect2 */(function(_1vm/* s1vkr */){
        var _1vn/* s1vks */ = E(_1vm/* s1vkr */);
        return (_1vn/* s1vks */._==2) ? (!B(_J9/* GHC.Base.eqString */(_1vn/* s1vks */.a, _1uR/* GHC.Read.lvl6 */))) ? new T0(2) : E(_1vh/* s1vkj */) : new T0(2);
      }));
    }),
    _1vo/* s1vkw */ = function(_1vp/* s1vkx */){
      return E(_1vg/* s1vki */);
    };
    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1vq/* s1vky */){
      return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1vq/* s1vky */, _1vo/* s1vkw */);});
    }), new T(function(){
      return new T1(1,B(_12G/* GHC.Read.$wa3 */(_1vb/* s1vkd */, _1vf/* s1vkh */)));
    }));});
  };
  return new F(function(){return _1ve/* s1vke */(_1uU/* s1vjG */);});
},
_1vr/* a7 */ = function(_1vs/* s1vpn */, _1vt/* s1vpo */){
  return new F(function(){return _1vu/* GHC.Read.$wa19 */(_1vt/* s1vpo */);});
},
_1vu/* $wa19 */ = function(_1vv/* s1vpp */){
  var _1vw/* s1vpu */ = new T(function(){
    return B(_128/* Text.Read.Lex.expect2 */(function(_1vx/* s1vpr */){
      var _1vy/* s1vps */ = E(_1vx/* s1vpr */);
      if(_1vy/* s1vps */._==1){
        return new F(function(){return A1(_1vv/* s1vpp */,_1vy/* s1vps */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1vz/* s1vpv */ = function(_1vA/* s1vpw */){
    return E(_1vw/* s1vpu */);
  };
  return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1vB/* s1vpx */){
    return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1vB/* s1vpx */, _1vz/* s1vpv */);});
  }), new T(function(){
    return B(_1uS/* GHC.Read.$wa */(_1uO/* GHC.Read.$fReadChar2 */, _1vv/* s1vpp */));
  }))), new T(function(){
    return new T1(1,B(_12G/* GHC.Read.$wa3 */(_1vr/* GHC.Read.a7 */, _1vv/* s1vpp */)));
  }));});
},
_1vC/* $fReadChar1 */ = function(_1vD/* s1vpF */, _1vE/* s1vpG */){
  return new F(function(){return _1vu/* GHC.Read.$wa19 */(_1vE/* s1vpG */);});
},
_1vF/* $fRead[]3 */ = function(_1vG/* s1vpI */, _1vH/* s1vpJ */){
  return new F(function(){return _1uS/* GHC.Read.$wa */(_1vC/* GHC.Read.$fReadChar1 */, _1vH/* s1vpJ */);});
},
_1vI/* $fRead[]5 */ = new T(function(){
  return B(_1uS/* GHC.Read.$wa */(_1vC/* GHC.Read.$fReadChar1 */, _RO/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1vJ/* $fRead[]4 */ = function(_1vK/* B1 */){
  return new F(function(){return _Py/* Text.ParserCombinators.ReadP.run */(_1vI/* GHC.Read.$fRead[]5 */, _1vK/* B1 */);});
},
_1vL/* $fReadChar4 */ = new T(function(){
  return B(_1vu/* GHC.Read.$wa19 */(_RO/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1vM/* $fReadChar3 */ = function(_1vK/* B1 */){
  return new F(function(){return _Py/* Text.ParserCombinators.ReadP.run */(_1vL/* GHC.Read.$fReadChar4 */, _1vK/* B1 */);});
},
_1vN/* $fRead[]_$s$creadsPrec1 */ = function(_1vO/* s1vpH */, _1vK/* B1 */){
  return new F(function(){return _1vM/* GHC.Read.$fReadChar3 */(_1vK/* B1 */);});
},
_1vP/* $fRead[]_$s$fRead[]1 */ = new T4(0,_1vN/* GHC.Read.$fRead[]_$s$creadsPrec1 */,_1vJ/* GHC.Read.$fRead[]4 */,_1vC/* GHC.Read.$fReadChar1 */,_1vF/* GHC.Read.$fRead[]3 */),
_1vQ/* $fRead(,)6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_1vR/* readPrec */ = function(_1vS/* s1vgA */){
  return E(E(_1vS/* s1vgA */).c);
},
_1vT/* $fRead(,)5 */ = function(_1vU/* s1vtd */, _1vV/* s1vte */, _1vW/* s1vtf */){
  var _1vX/* s1vtg */ = new T(function(){
    return B(_1vR/* GHC.Read.readPrec */(_1vV/* s1vte */));
  }),
  _1vY/* s1vth */ = new T(function(){
    return B(A2(_1vR/* GHC.Read.readPrec */,_1vU/* s1vtd */, _1vW/* s1vtf */));
  }),
  _1vZ/* s1vtz */ = function(_1w0/* s1vti */){
    var _1w1/* s1vty */ = function(_1w2/* s1vtj */){
      var _1w3/* s1vtk */ = new T(function(){
        var _1w4/* s1vtl */ = new T(function(){
          return B(A2(_1vX/* s1vtg */,_1vW/* s1vtf */, function(_1w5/* s1vtm */){
            return new F(function(){return A1(_1w0/* s1vti */,new T2(0,_1w2/* s1vtj */,_1w5/* s1vtm */));});
          }));
        });
        return B(_128/* Text.Read.Lex.expect2 */(function(_1w6/* s1vtp */){
          var _1w7/* s1vtq */ = E(_1w6/* s1vtp */);
          return (_1w7/* s1vtq */._==2) ? (!B(_J9/* GHC.Base.eqString */(_1w7/* s1vtq */.a, _1vQ/* GHC.Read.$fRead(,)6 */))) ? new T0(2) : E(_1w4/* s1vtl */) : new T0(2);
        }));
      }),
      _1w8/* s1vtu */ = function(_1w9/* s1vtv */){
        return E(_1w3/* s1vtk */);
      };
      return new T1(1,function(_1wa/* s1vtw */){
        return new F(function(){return A2(_10P/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1wa/* s1vtw */, _1w8/* s1vtu */);});
      });
    };
    return new F(function(){return A1(_1vY/* s1vth */,_1w1/* s1vty */);});
  };
  return E(_1vZ/* s1vtz */);
},
_1wb/* $wa2 */ = function(_1wc/* s1vuR */, _1wd/* s1vuS */, _1we/* s1vuT */){
  var _1wf/* s1vuU */ = function(_1vK/* B1 */){
    return new F(function(){return _1vT/* GHC.Read.$fRead(,)5 */(_1wc/* s1vuR */, _1wd/* s1vuS */, _1vK/* B1 */);});
  },
  _1wg/* s1vuV */ = function(_1wh/* s1vuX */, _1wi/* s1vuY */){
    return new F(function(){return _1wj/* s1vuW */(_1wi/* s1vuY */);});
  },
  _1wj/* s1vuW */ = function(_1wk/* s1vuZ */){
    return new F(function(){return _QI/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_12G/* GHC.Read.$wa3 */(_1wf/* s1vuU */, _1wk/* s1vuZ */))), new T(function(){
      return new T1(1,B(_12G/* GHC.Read.$wa3 */(_1wg/* s1vuV */, _1wk/* s1vuZ */)));
    }));});
  };
  return new F(function(){return _1wj/* s1vuW */(_1we/* s1vuT */);});
},
_1wl/* $s$fRead(,)3 */ = function(_1wm/* sq8R */, _1wn/* sq8S */){
  return new F(function(){return _1wb/* GHC.Read.$wa2 */(_1vP/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1vP/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1wn/* sq8S */);});
},
_1wo/* lvl10 */ = new T(function(){
  return B(_1uS/* GHC.Read.$wa */(_1wl/* Main.$s$fRead(,)3 */, _18G/* Text.Read.readEither5 */));
}),
_1wp/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Error generating tabs"));
}),
_1wq/* a */ = 0,
_1wr/* lookup */ = function(_1ws/* s9uF */, _1wt/* s9uG */, _1wu/* s9uH */){
  while(1){
    var _1wv/* s9uI */ = E(_1wu/* s9uH */);
    if(!_1wv/* s9uI */._){
      return __Z/* EXTERNAL */;
    }else{
      var _1ww/* s9uL */ = E(_1wv/* s9uI */.a);
      if(!B(A3(_Vb/* GHC.Classes.== */,_1ws/* s9uF */, _1wt/* s9uG */, _1ww/* s9uL */.a))){
        _1wu/* s9uH */ = _1wv/* s9uI */.b;
        continue;
      }else{
        return new T1(1,_1ww/* s9uL */.b);
      }
    }
  }
},
_1wx/* getMaybeNumberFIUnitValue */ = function(_1wy/* s3sW */, _1wz/* s3sX */){
  var _1wA/* s3sY */ = E(_1wz/* s3sX */);
  if(!_1wA/* s3sY */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1wB/* s3t0 */ = E(_1wy/* s3sW */);
    if(_1wB/* s3t0 */._==3){
      var _1wC/* s3t4 */ = E(_1wB/* s3t0 */.b);
      switch(_1wC/* s3t4 */._){
        case 0:
          return new T1(1,_1wC/* s3t4 */.a);
        case 1:
          return new F(function(){return _1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1wB/* s3t0 */.a).b)), _Pq/* FormEngine.FormItem.nfiUnitId1 */));
          }), _1wA/* s3sY */.a);});
          break;
        default:
          return __Z/* EXTERNAL */;
      }
    }else{
      return E(_1bY/* FormEngine.FormItem.nfiUnit1 */);
    }
  }
},
_1wD/* fiId */ = function(_1wE/* s5uj */){
  return new F(function(){return _4Q/* FormEngine.FormItem.numbering2text */(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1wE/* s5uj */)).b);});
},
_1wF/* isCheckboxChecked1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("on"));
}),
_1wG/* isCheckboxChecked */ = function(_1wH/* s3sP */, _1wI/* s3sQ */){
  var _1wJ/* s3sR */ = E(_1wI/* s3sQ */);
  if(!_1wJ/* s3sR */._){
    return false;
  }else{
    var _1wK/* s3sU */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_1wD/* FormEngine.FormItem.fiId */(_1wH/* s3sP */));
    }), _1wJ/* s3sR */.a));
    if(!_1wK/* s3sU */._){
      return false;
    }else{
      return new F(function(){return _J9/* GHC.Base.eqString */(_1wK/* s3sU */.a, _1wF/* FormEngine.FormData.isCheckboxChecked1 */);});
    }
  }
},
_1wL/* isOptionSelected */ = function(_1wM/* s3sn */, _1wN/* s3so */, _1wO/* s3sp */){
  var _1wP/* s3sq */ = E(_1wO/* s3sp */);
  if(!_1wP/* s3sq */._){
    return false;
  }else{
    var _1wQ/* s3sD */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4r/* FormEngine.FormItem.fiDescriptor */(_1wN/* s3so */)).b));
    }), _1wP/* s3sq */.a));
    if(!_1wQ/* s3sD */._){
      return false;
    }else{
      var _1wR/* s3sE */ = _1wQ/* s3sD */.a,
      _1wS/* s3sF */ = E(_1wM/* s3sn */);
      if(!_1wS/* s3sF */._){
        return new F(function(){return _J9/* GHC.Base.eqString */(_1wR/* s3sE */, _1wS/* s3sF */.a);});
      }else{
        return new F(function(){return _J9/* GHC.Base.eqString */(_1wR/* s3sE */, _1wS/* s3sF */.b);});
      }
    }
  }
},
_1wT/* mapMaybe */ = function(_1wU/*  s7rs */, _1wV/*  s7rt */){
  while(1){
    var _1wW/*  mapMaybe */ = B((function(_1wX/* s7rs */, _1wY/* s7rt */){
      var _1wZ/* s7ru */ = E(_1wY/* s7rt */);
      if(!_1wZ/* s7ru */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1x0/* s7rw */ = _1wZ/* s7ru */.b,
        _1x1/* s7rx */ = B(A1(_1wX/* s7rs */,_1wZ/* s7ru */.a));
        if(!_1x1/* s7rx */._){
          var _1x2/*   s7rs */ = _1wX/* s7rs */;
          _1wU/*  s7rs */ = _1x2/*   s7rs */;
          _1wV/*  s7rt */ = _1x0/* s7rw */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1x1/* s7rx */.a,new T(function(){
            return B(_1wT/* Data.Maybe.mapMaybe */(_1wX/* s7rs */, _1x0/* s7rw */));
          }));
        }
      }
    })(_1wU/*  s7rs */, _1wV/*  s7rt */));
    if(_1wW/*  mapMaybe */!=__continue/* EXTERNAL */){
      return _1wW/*  mapMaybe */;
    }
  }
},
_1x3/* maybeStr2maybeFloat2 */ = new T(function(){
  return B(A3(_13a/* GHC.Read.$fReadFloat7 */,_18x/* GHC.Read.$fReadFloat_$sconvertFrac */, _12F/* Text.ParserCombinators.ReadPrec.minPrec */, _RO/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1x4/* maybeStr2maybeFloat1 */ = function(_1x5/* s6Ub */){
  var _1x6/* s6Uc */ = B(_Py/* Text.ParserCombinators.ReadP.run */(_1x3/* FormEngine.FormElement.FormElement.maybeStr2maybeFloat2 */, _1x5/* s6Ub */));
  return (_1x6/* s6Uc */._==0) ? __Z/* EXTERNAL */ : (E(_1x6/* s6Uc */.b)._==0) ? new T1(1,E(_1x6/* s6Uc */.a).a) : __Z/* EXTERNAL */;
},
_1x7/* makeElem */ = function(_1x8/* s6UP */, _1x9/* s6UQ */, _1xa/* s6UR */, _1xb/* s6US */){
  var _1xc/* s6UT */ = E(_1xb/* s6US */);
  switch(_1xc/* s6UT */._){
    case 0:
      var _1xd/* s6Vh */ = new T(function(){
        var _1xe/* s6Vb */ = E(_1x9/* s6UQ */);
        if(!_1xe/* s6Vb */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xe/* s6Vb */.a).b);
          }));
        }
      }),
      _1xf/* s6Va */ = new T(function(){
        var _1xg/* s6UV */ = E(_1xa/* s6UR */);
        if(!_1xg/* s6UV */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1xh/* s6V8 */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1xc/* s6UT */.a).b));
          }), _1xg/* s6UV */.a));
          if(!_1xh/* s6V8 */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1xh/* s6V8 */.a);
          }
        }
      });
      return new T1(1,new T4(1,_1xc/* s6UT */,_1xf/* s6Va */,_1xd/* s6Vh */,_1x8/* s6UP */));
    case 1:
      var _1xi/* s6VG */ = new T(function(){
        var _1xj/* s6VA */ = E(_1x9/* s6UQ */);
        if(!_1xj/* s6VA */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xj/* s6VA */.a).b);
          }));
        }
      }),
      _1xk/* s6Vz */ = new T(function(){
        var _1xl/* s6Vk */ = E(_1xa/* s6UR */);
        if(!_1xl/* s6Vk */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1xm/* s6Vx */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1xc/* s6UT */.a).b));
          }), _1xl/* s6Vk */.a));
          if(!_1xm/* s6Vx */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1xm/* s6Vx */.a);
          }
        }
      });
      return new T1(1,new T4(2,_1xc/* s6UT */,_1xk/* s6Vz */,_1xi/* s6VG */,_1x8/* s6UP */));
    case 2:
      var _1xn/* s6W5 */ = new T(function(){
        var _1xo/* s6VZ */ = E(_1x9/* s6UQ */);
        if(!_1xo/* s6VZ */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xo/* s6VZ */.a).b);
          }));
        }
      }),
      _1xp/* s6VY */ = new T(function(){
        var _1xq/* s6VJ */ = E(_1xa/* s6UR */);
        if(!_1xq/* s6VJ */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1xr/* s6VW */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1xc/* s6UT */.a).b));
          }), _1xq/* s6VJ */.a));
          if(!_1xr/* s6VW */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1xr/* s6VW */.a);
          }
        }
      });
      return new T1(1,new T4(3,_1xc/* s6UT */,_1xp/* s6VY */,_1xn/* s6W5 */,_1x8/* s6UP */));
    case 3:
      var _1xs/* s6Ww */ = new T(function(){
        var _1xt/* s6Wq */ = E(_1x9/* s6UQ */);
        if(!_1xt/* s6Wq */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xt/* s6Wq */.a).b);
          }));
        }
      }),
      _1xu/* s6Wo */ = new T(function(){
        var _1xv/* s6W9 */ = E(_1xa/* s6UR */);
        if(!_1xv/* s6W9 */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1xw/* s6Wm */ = B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1xc/* s6UT */.a).b));
          }), _1xv/* s6W9 */.a));
          if(!_1xw/* s6Wm */._){
            return __Z/* EXTERNAL */;
          }else{
            return B(_1x4/* FormEngine.FormElement.FormElement.maybeStr2maybeFloat1 */(_1xw/* s6Wm */.a));
          }
        }
      });
      return new T1(1,new T5(4,_1xc/* s6UT */,_1xu/* s6Wo */,new T(function(){
        return B(_1wx/* FormEngine.FormData.getMaybeNumberFIUnitValue */(_1xc/* s6UT */, _1xa/* s6UR */));
      }),_1xs/* s6Ww */,_1x8/* s6UP */));
    case 4:
      return new T1(1,new T2(5,_1xc/* s6UT */,_1x8/* s6UP */));
    case 5:
      var _1xx/* s6WD */ = new T(function(){
        var _1xy/* s6WE */ = E(_1x9/* s6UQ */);
        if(!_1xy/* s6WE */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xy/* s6WE */.a).b);
          }));
        }
      }),
      _1xz/* s6WK */ = new T(function(){
        return new T4(6,_1xc/* s6UT */,_1xA/* s6WL */,_1xx/* s6WD */,_1x8/* s6UP */);
      }),
      _1xA/* s6WL */ = new T(function(){
        var _1xB/* s6WW */ = function(_1xC/* s6WM */){
          var _1xD/* s6WN */ = E(_1xC/* s6WM */);
          if(!_1xD/* s6WN */._){
            return new T2(0,_1xD/* s6WN */,new T(function(){
              return B(_1wL/* FormEngine.FormData.isOptionSelected */(_1xD/* s6WN */, _1xc/* s6UT */, _1xa/* s6UR */));
            }));
          }else{
            var _1xE/* s6WV */ = new T(function(){
              return B(_1wT/* Data.Maybe.mapMaybe */(function(_1iB/* B1 */){
                return new F(function(){return _1x7/* FormEngine.FormElement.FormElement.makeElem */(_1xz/* s6WK */, _1x9/* s6UQ */, _1xa/* s6UR */, _1iB/* B1 */);});
              }, _1xD/* s6WN */.c));
            });
            return new T3(1,_1xD/* s6WN */,new T(function(){
              return B(_1wL/* FormEngine.FormData.isOptionSelected */(_1xD/* s6WN */, _1xc/* s6UT */, _1xa/* s6UR */));
            }),_1xE/* s6WV */);
          }
        };
        return B(_2S/* GHC.Base.map */(_1xB/* s6WW */, _1xc/* s6UT */.b));
      });
      return new T1(1,_1xz/* s6WK */);
    case 6:
      var _1xF/* s6Xj */ = new T(function(){
        var _1xG/* s6Xd */ = E(_1x9/* s6UQ */);
        if(!_1xG/* s6Xd */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xG/* s6Xd */.a).b);
          }));
        }
      }),
      _1xH/* s6Xc */ = new T(function(){
        var _1xI/* s6WZ */ = E(_1xa/* s6UR */);
        if(!_1xI/* s6WZ */._){
          return __Z/* EXTERNAL */;
        }else{
          return B(_1wr/* GHC.List.lookup */(_RB/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1xc/* s6UT */.a).b));
          }), _1xI/* s6WZ */.a));
        }
      });
      return new T1(1,new T4(7,_1xc/* s6UT */,_1xH/* s6Xc */,_1xF/* s6Xj */,_1x8/* s6UP */));
    case 7:
      return __Z/* EXTERNAL */;
    case 8:
      var _1xJ/* s6Xq */ = new T(function(){
        var _1xK/* s6Xr */ = E(_1x9/* s6UQ */);
        if(!_1xK/* s6Xr */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xK/* s6Xr */.a).b);
          }));
        }
      }),
      _1xL/* s6Xx */ = new T(function(){
        return new T4(8,_1xc/* s6UT */,_1xM/* s6Xy */,_1xJ/* s6Xq */,_1x8/* s6UP */);
      }),
      _1xM/* s6Xy */ = new T(function(){
        return B(_1wT/* Data.Maybe.mapMaybe */(function(_1iB/* B1 */){
          return new F(function(){return _1x7/* FormEngine.FormElement.FormElement.makeElem */(_1xL/* s6Xx */, _1x9/* s6UQ */, _1xa/* s6UR */, _1iB/* B1 */);});
        }, _1xc/* s6UT */.c));
      });
      return new T1(1,_1xL/* s6Xx */);
    case 9:
      var _1xN/* s6XD */ = new T(function(){
        var _1xO/* s6XE */ = E(_1x9/* s6UQ */);
        if(!_1xO/* s6XE */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xO/* s6XE */.a).b);
          }));
        }
      }),
      _1xP/* s6XL */ = new T(function(){
        return new T5(9,_1xc/* s6UT */,new T(function(){
          return B(_1wG/* FormEngine.FormData.isCheckboxChecked */(_1xc/* s6UT */, _1xa/* s6UR */));
        }),_1xQ/* s6XM */,_1xN/* s6XD */,_1x8/* s6UP */);
      }),
      _1xQ/* s6XM */ = new T(function(){
        return B(_1wT/* Data.Maybe.mapMaybe */(function(_1iB/* B1 */){
          return new F(function(){return _1x7/* FormEngine.FormElement.FormElement.makeElem */(_1xP/* s6XL */, _1x9/* s6UQ */, _1xa/* s6UR */, _1iB/* B1 */);});
        }, _1xc/* s6UT */.c));
      });
      return new T1(1,_1xP/* s6XL */);
    case 10:
      var _1xR/* s6XR */ = new T(function(){
        var _1xS/* s6XS */ = E(_1x9/* s6UQ */);
        if(!_1xS/* s6XS */._){
          return __Z/* EXTERNAL */;
        }else{
          return new T1(1,new T(function(){
            return E(E(_1xS/* s6XS */.a).b);
          }));
        }
      }),
      _1xT/* s6XY */ = new T(function(){
        return new T2(0,_1xU/* s6Y1 */,_1wq/* FormEngine.FormElement.FormElement.a */);
      }),
      _1xV/* s6XZ */ = new T(function(){
        return new T2(1,_1xT/* s6XY */,_I/* GHC.Types.[] */);
      }),
      _1xW/* s6Y0 */ = new T(function(){
        return new T4(10,_1xc/* s6UT */,_1xV/* s6XZ */,_1xR/* s6XR */,_1x8/* s6UP */);
      }),
      _1xU/* s6Y1 */ = new T(function(){
        return B(_1wT/* Data.Maybe.mapMaybe */(function(_1iB/* B1 */){
          return new F(function(){return _1x7/* FormEngine.FormElement.FormElement.makeElem */(_1xW/* s6Y0 */, new T1(1,_1xT/* s6XY */), _1xa/* s6UR */, _1iB/* B1 */);});
        }, _1xc/* s6UT */.c));
      });
      return new T1(1,_1xW/* s6Y0 */);
    case 11:
      return new T1(1,new T2(11,_1xc/* s6UT */,_1x8/* s6UP */));
    default:
      return new T1(1,new T2(12,_1xc/* s6UT */,_1x8/* s6UP */));
  }
},
_1xX/* onResize2 */ = "(function (ev, jq) { jq.resize(ev); })",
_1xY/* onResize1 */ = function(_1xZ/* stui */, _1y0/* stuj */, _/* EXTERNAL */){
  var _1y1/* stuv */ = __createJSFunc/* EXTERNAL */(2, function(_1y2/* stum */, _/* EXTERNAL */){
    var _1y3/* stuo */ = B(A2(E(_1xZ/* stui */),_1y2/* stum */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1y4/* stuy */ = E(_1y0/* stuj */),
  _1y5/* stuD */ = eval/* EXTERNAL */(E(_1xX/* FormEngine.JQuery.onResize2 */)),
  _1y6/* stuL */ = __app2/* EXTERNAL */(E(_1y5/* stuD */), _1y1/* stuv */, _1y4/* stuy */);
  return _1y4/* stuy */;
},
_1y7/* onScroll2 */ = "(function (ev, jq) { jq.scroll(ev); })",
_1y8/* onScroll1 */ = function(_1y9/* stuR */, _1ya/* stuS */, _/* EXTERNAL */){
  var _1yb/* stv4 */ = __createJSFunc/* EXTERNAL */(2, function(_1yc/* stuV */, _/* EXTERNAL */){
    var _1yd/* stuX */ = B(A2(E(_1y9/* stuR */),_1yc/* stuV */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1ye/* stv7 */ = E(_1ya/* stuS */),
  _1yf/* stvc */ = eval/* EXTERNAL */(E(_1y7/* FormEngine.JQuery.onScroll2 */)),
  _1yg/* stvk */ = __app2/* EXTERNAL */(E(_1yf/* stvc */), _1yb/* stv4 */, _1ye/* stv7 */);
  return _1ye/* stv7 */;
},
_1yh/* pageTabGroup17 */ = 600,
_1yi/* pageTabGroup16 */ = new T2(1,_1yh/* Page.pageTabGroup17 */,_I/* GHC.Types.[] */),
_1yj/* pageTabGroup15 */ = new T2(1,_1yi/* Page.pageTabGroup16 */,_2H/* Page.pageTabGroup10 */),
_1yk/* pageTabGroup14 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1yj/* Page.pageTabGroup15 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1yl/* pageTabGroup13 */ = new T2(7,_1yk/* Page.pageTabGroup14 */,_I/* GHC.Types.[] */),
_1ym/* mQuestionnaireTab */ = new T3(0,_1yl/* Page.pageTabGroup13 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1yn/* pageTabGroup12 */ = 700,
_1yo/* pageTabGroup11 */ = new T2(1,_1yn/* Page.pageTabGroup12 */,_I/* GHC.Types.[] */),
_1yp/* pageTabGroup9 */ = new T2(1,_1yo/* Page.pageTabGroup11 */,_2H/* Page.pageTabGroup10 */),
_1yq/* pageTabGroup8 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1yp/* Page.pageTabGroup9 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1yr/* pageTabGroup7 */ = new T2(7,_1yq/* Page.pageTabGroup8 */,_I/* GHC.Types.[] */),
_1ys/* tQuestionnaireTab */ = new T3(0,_1yr/* Page.pageTabGroup7 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1yt/* pageTabGroup6 */ = new T2(1,_1ys/* Page.tQuestionnaireTab */,_I/* GHC.Types.[] */),
_1yu/* pageTabGroup5 */ = new T2(1,_1ym/* Page.mQuestionnaireTab */,_1yt/* Page.pageTabGroup6 */),
_1yv/* pageTabGroup22 */ = 500,
_1yw/* pageTabGroup21 */ = new T2(1,_1yv/* Page.pageTabGroup22 */,_I/* GHC.Types.[] */),
_1yx/* pageTabGroup20 */ = new T2(1,_1yw/* Page.pageTabGroup21 */,_2H/* Page.pageTabGroup10 */),
_1yy/* pageTabGroup19 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1yx/* Page.pageTabGroup20 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1yz/* pageTabGroup18 */ = new T2(7,_1yy/* Page.pageTabGroup19 */,_I/* GHC.Types.[] */),
_1yA/* rolesTab */ = new T3(0,_1yz/* Page.pageTabGroup18 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1yB/* pageTabGroup4 */ = new T2(1,_1yA/* Page.rolesTab */,_1yu/* Page.pageTabGroup5 */),
_1yC/* pageTabGroup3 */ = new T2(1,_3R/* Page.dataTab */,_1yB/* Page.pageTabGroup4 */),
_1yD/* pageTabGroup2 */ = new T2(1,_3Z/* Page.lifecycleTab */,_1yC/* Page.pageTabGroup3 */),
_1yE/* pageTabGroup1 */ = new T2(1,_2N/* Page.actionTab */,_1yD/* Page.pageTabGroup2 */),
_1yF/* pageTabGroup42 */ = 100,
_1yG/* pageTabGroup41 */ = new T2(1,_1yF/* Page.pageTabGroup42 */,_I/* GHC.Types.[] */),
_1yH/* pageTabGroup40 */ = new T2(1,_1yG/* Page.pageTabGroup41 */,_2H/* Page.pageTabGroup10 */),
_1yI/* pageTabGroup39 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1yH/* Page.pageTabGroup40 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1yJ/* pageTabGroup38 */ = new T2(7,_1yI/* Page.pageTabGroup39 */,_I/* GHC.Types.[] */),
_1yK/* visionTab */ = new T3(0,_1yJ/* Page.pageTabGroup38 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1yL/* pageTabGroup */ = new T2(1,_1yK/* Page.visionTab */,_1yE/* Page.pageTabGroup1 */),
_1yM/* getWidth_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.width(); })");
}),
_1yN/* resizeHandler2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".svg-help"));
}),
_1yO/* resizeHandler_paneSel */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".desc-subpane"));
}),
_1yP/* setWidth_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (val, jq) { jq.width(val); return jq; })");
}),
_1yQ/* $wa */ = function(_/* EXTERNAL */){
  var _1yR/* sqaC */ = __app0/* EXTERNAL */(E(_51/* FormEngine.JQuery.getWindow_f1 */)),
  _1yS/* sqaI */ = __app1/* EXTERNAL */(E(_1yM/* FormEngine.JQuery.getWidth_f1 */), _1yR/* sqaC */),
  _1yT/* sqaL */ = B(_56/* FormEngine.JQuery.select1 */(_1yO/* Main.resizeHandler_paneSel */, _/* EXTERNAL */)),
  _1yU/* sqaP */ = Number/* EXTERNAL */(_1yS/* sqaI */),
  _1yV/* sqaT */ = jsTrunc/* EXTERNAL */(_1yU/* sqaP */),
  _1yW/* sqb4 */ = E(_1yP/* FormEngine.JQuery.setWidth_f1 */),
  _1yX/* sqb7 */ = __app2/* EXTERNAL */(_1yW/* sqb4 */, _1yV/* sqaT */-790|0, E(_1yT/* sqaL */)),
  _1yY/* sqba */ = B(_56/* FormEngine.JQuery.select1 */(_1yN/* Main.resizeHandler2 */, _/* EXTERNAL */)),
  _1yZ/* sqbg */ = __app2/* EXTERNAL */(_1yW/* sqb4 */, _1yV/* sqaT */-795|0, E(_1yY/* sqba */));
  return _0/* GHC.Tuple.() */;
},
_1z0/* resizeHandler1 */ = function(_1z1/* sqbj */, _/* EXTERNAL */){
  return new F(function(){return _1yQ/* Main.$wa */(_/* EXTERNAL */);});
},
_1z2/* time2 */ = "(function (label) { console.time(label); })",
_1z3/* time1 */ = function(_1z4/* stsf */, _/* EXTERNAL */){
  var _1z5/* stsp */ = eval/* EXTERNAL */(E(_1z2/* FormEngine.JQuery.time2 */)),
  _1z6/* stsx */ = __app1/* EXTERNAL */(E(_1z5/* stsp */), toJSStr/* EXTERNAL */(E(_1z4/* stsf */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1z7/* timeEnd2 */ = "(function (label) { console.timeEnd(label); })",
_1z8/* timeEnd1 */ = function(_1z9/* strR */, _/* EXTERNAL */){
  var _1za/* sts1 */ = eval/* EXTERNAL */(E(_1z7/* FormEngine.JQuery.timeEnd2 */)),
  _1zb/* sts9 */ = __app1/* EXTERNAL */(E(_1za/* sts1 */), toJSStr/* EXTERNAL */(E(_1z9/* strR */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1zc/* lvl14 */ = function(_1zd/* sqbO */, _/* EXTERNAL */){
  var _1ze/* sqbR */ = new T(function(){
    var _1zf/* sqbW */ = B(_Pr/* Text.Read.readEither6 */(B(_Py/* Text.ParserCombinators.ReadP.run */(_1wo/* Main.lvl10 */, new T(function(){
      var _1zg/* sqbS */ = E(_1zd/* sqbO */);
      if(!_1zg/* sqbS */._){
        return __Z/* EXTERNAL */;
      }else{
        return E(_1zg/* sqbS */.a);
      }
    })))));
    if(!_1zf/* sqbW */._){
      return __Z/* EXTERNAL */;
    }else{
      if(!E(_1zf/* sqbW */.b)._){
        return new T1(1,_1zf/* sqbW */.a);
      }else{
        return __Z/* EXTERNAL */;
      }
    }
  }),
  _1zh/* sqc9 */ = function(_1zi/* sqc2 */){
    var _1zj/* sqc3 */ = E(_1zi/* sqc2 */);
    if(_1zj/* sqc3 */._==7){
      var _1zk/* sqc6 */ = new T(function(){
        return new T3(0,_1zj/* sqc3 */,_1zl/* sqc7 */,_2G/* GHC.Types.False */);
      }),
      _1zl/* sqc7 */ = new T(function(){
        return B(_1wT/* Data.Maybe.mapMaybe */(function(_1zm/* B1 */){
          return new F(function(){return _1x7/* FormEngine.FormElement.FormElement.makeElem */(_1zk/* sqc6 */, _2o/* GHC.Base.Nothing */, _1ze/* sqbR */, _1zm/* B1 */);});
        }, _1zj/* sqc3 */.b));
      });
      return new T1(1,_1zk/* sqc6 */);
    }else{
      return __Z/* EXTERNAL */;
    }
  },
  _1zn/* sqbQ */ = B(_2S/* GHC.Base.map */(_1zh/* sqc9 */, _Hx/* FormStructure.FormStructure.formItems */));
  if(!B(_1uz/* Main.go */(_1zn/* sqbQ */))){
    var _1zo/* sqcb */ = B(_1z3/* FormEngine.JQuery.time1 */(_1uC/* Main.lvl */, _/* EXTERNAL */)),
    _1zp/* sqce */ = new T(function(){
      return B(_5I/* Data.Maybe.catMaybes1 */(_1zn/* sqbQ */));
    }),
    _1zq/* sqcf */ = B(_1tT/* Form.generateQuestionnaire1 */(_1zp/* sqce */, _/* EXTERNAL */)),
    _1zr/* sqci */ = B(_1z8/* FormEngine.JQuery.timeEnd1 */(_1uC/* Main.lvl */, _/* EXTERNAL */)),
    _1zs/* sqcl */ = E(_51/* FormEngine.JQuery.getWindow_f1 */),
    _1zt/* sqco */ = __app0/* EXTERNAL */(_1zs/* sqcl */),
    _1zu/* sqcv */ = B(_1y8/* FormEngine.JQuery.onScroll1 */(function(_1zv/* sqcr */, _/* EXTERNAL */){
      return new F(function(){return _59/* Main.$wa1 */(_1zp/* sqce */, _/* EXTERNAL */);});
    }, _1zt/* sqco */, _/* EXTERNAL */)),
    _1zw/* sqcz */ = __app0/* EXTERNAL */(_1zs/* sqcl */),
    _1zx/* sqcD */ = B(_1xY/* FormEngine.JQuery.onResize1 */(_1z0/* Main.resizeHandler1 */, _1zw/* sqcz */, _/* EXTERNAL */)),
    _1zy/* sqcH */ = __app0/* EXTERNAL */(_1zs/* sqcl */),
    _1zz/* sqcK */ = B(_5E/* FormEngine.JQuery.$wa17 */(_1zy/* sqcH */, _/* EXTERNAL */)),
    _1zA/* sqcN */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_1yK/* Page.visionTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }else{
    var _1zB/* sqcQ */ = B(_5Q/* FormEngine.JQuery.errorIO1 */(_1wp/* Main.lvl13 */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_1zC/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_investigator"));
}),
_1zD/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_manager"));
}),
_1zE/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_steward"));
}),
_1zF/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_custodian"));
}),
_1zG/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_curator"));
}),
_1zH/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_consumer"));
}),
_1zI/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_expert"));
}),
_1zJ/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_producer"));
}),
_1zK/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_public"));
}),
_1zL/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_secondary"));
}),
_1zM/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_primary"));
}),
_1zN/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_raw"));
}),
_1zO/* overlay2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_1zP/* overlay3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("body"));
}),
_1zQ/* overlay4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("div"));
}),
_1zR/* $w$j */ = function(_/* EXTERNAL */, _1zS/* sOMi */){
  var _1zT/* sOMj */ = B(_1e9/* FormEngine.JQuery.$wa9 */(_1zQ/* Overlay.overlay4 */, _1zS/* sOMi */, _/* EXTERNAL */)),
  _1zU/* sOMm */ = B(_56/* FormEngine.JQuery.select1 */(_1zP/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1zV/* sOMu */ = __app1/* EXTERNAL */(E(_4Z/* FormEngine.JQuery.getScrollTop_f1 */), E(_1zU/* sOMm */)),
  _1zW/* sOMy */ = Number/* EXTERNAL */(_1zV/* sOMu */),
  _1zX/* sOMC */ = jsTrunc/* EXTERNAL */(_1zW/* sOMy */);
  return new F(function(){return _43/* FormEngine.JQuery.$wa2 */(_1zO/* Overlay.overlay2 */, B(_4e/* GHC.Show.$wshowSignedInt */(0, _1zX/* sOMC */+25|0, _I/* GHC.Types.[] */)), E(_1zT/* sOMj */), _/* EXTERNAL */);});
},
_1zY/* getCss2 */ = "(function (key, jq) { return jq.css(key); })",
_1zZ/* $wa11 */ = function(_1A0/* stKF */, _1A1/* stKG */, _/* EXTERNAL */){
  var _1A2/* stKQ */ = eval/* EXTERNAL */(E(_1zY/* FormEngine.JQuery.getCss2 */)),
  _1A3/* stKY */ = __app2/* EXTERNAL */(E(_1A2/* stKQ */), toJSStr/* EXTERNAL */(E(_1A0/* stKF */)), _1A1/* stKG */);
  return new T(function(){
    return String/* EXTERNAL */(_1A3/* stKY */);
  });
},
_1A4/* getHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (jq) { return jq.height(); })");
}),
_1A5/* hideJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hidden"));
}),
_1A6/* hideJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1A7/* overlay5 */ = "visible",
_1A8/* overlay6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1A9/* setHeight_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (val, jq) { jq.height(val); return jq; })");
}),
_1Aa/* showJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visible"));
}),
_1Ab/* overlay1 */ = function(_1Ac/* sOMJ */, _/* EXTERNAL */){
  var _1Ad/* sOMM */ = B(_56/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", _1Ac/* sOMJ */)), _/* EXTERNAL */)),
  _1Ae/* sOMP */ = B(_56/* FormEngine.JQuery.select1 */(_1zP/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1Af/* sOMX */ = __app1/* EXTERNAL */(E(_1A4/* FormEngine.JQuery.getHeight_f1 */), E(_1Ae/* sOMP */)),
  _1Ag/* sON1 */ = Number/* EXTERNAL */(_1Af/* sOMX */),
  _1Ah/* sON5 */ = jsTrunc/* EXTERNAL */(_1Ag/* sON1 */),
  _1Ai/* sONf */ = __app2/* EXTERNAL */(E(_1A9/* FormEngine.JQuery.setHeight_f1 */), _1Ah/* sON5 */, E(_1Ad/* sOMM */)),
  _1Aj/* sONi */ = B(_1zZ/* FormEngine.JQuery.$wa11 */(_1A8/* Overlay.overlay6 */, _1Ai/* sONf */, _/* EXTERNAL */)),
  _1Ak/* sONq */ = strEq/* EXTERNAL */(E(_1Aj/* sONi */), E(_1A7/* Overlay.overlay5 */));
  if(!E(_1Ak/* sONq */)){
    var _1Al/* sONz */ = B(_43/* FormEngine.JQuery.$wa2 */(_1A6/* FormEngine.JQuery.hideJq3 */, _1Aa/* FormEngine.JQuery.showJq2 */, _1Ai/* sONf */, _/* EXTERNAL */));
    return new F(function(){return _1zR/* Overlay.$w$j */(_/* EXTERNAL */, E(_1Al/* sONz */));});
  }else{
    var _1Am/* sONu */ = B(_43/* FormEngine.JQuery.$wa2 */(_1A6/* FormEngine.JQuery.hideJq3 */, _1A5/* FormEngine.JQuery.hideJq2 */, _1Ai/* sONf */, _/* EXTERNAL */));
    return new F(function(){return _1zR/* Overlay.$w$j */(_/* EXTERNAL */, E(_1Am/* sONu */));});
  }
},
_1An/* ready_f1 */ = new T(function(){
  return eval/* EXTERNAL */("(function (f) { jQuery(document).ready(f); })");
}),
_1Ao/* tinkerDiagSvgConsumer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_consumer"));
}),
_1Ap/* tinkerDiagSvgConsumer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tx/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1Ao/* DiagramDecorator.tinkerDiagSvgConsumer3 */, _/* EXTERNAL */);});
},
_1Aq/* tinkerDiagSvgConsumer1 */ = function(_1Ar/* seP9 */, _/* EXTERNAL */){
  return new F(function(){return _1Ap/* DiagramDecorator.tinkerDiagSvgConsumer2 */(_/* EXTERNAL */);});
},
_1As/* tinkerDiagSvgCurator7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_curator"));
}),
_1At/* tinkerDiagSvgCurator2 */ = function(_/* EXTERNAL */){
  var _1Au/* sePN */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1Av/* sePQ */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tx/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1Aw/* sePT */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1Ax/* sePW */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tA/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1Ay/* sePZ */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tz/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ty/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1As/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */);});
},
_1Az/* tinkerDiagSvgCurator1 */ = function(_1AA/* seQ2 */, _/* EXTERNAL */){
  return new F(function(){return _1At/* DiagramDecorator.tinkerDiagSvgCurator2 */(_/* EXTERNAL */);});
},
_1AB/* tinkerDiagSvgCustodian3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_custodian"));
}),
_1AC/* tinkerDiagSvgCustodian2 */ = function(_/* EXTERNAL */){
  var _1AD/* seQ4 */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1AB/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */)),
  _1AE/* seQ7 */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tA/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1AB/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tz/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1AB/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */);});
},
_1AF/* tinkerDiagSvgCustodian1 */ = function(_1AG/* seQa */, _/* EXTERNAL */){
  return new F(function(){return _1AC/* DiagramDecorator.tinkerDiagSvgCustodian2 */(_/* EXTERNAL */);});
},
_1AH/* tinkerDiagSvgExpert3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_expert"));
}),
_1AI/* tinkerDiagSvgExpert2 */ = function(_/* EXTERNAL */){
  var _1AJ/* sePI */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1AH/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1AH/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */);});
},
_1AK/* tinkerDiagSvgExpert1 */ = function(_1AL/* sePL */, _/* EXTERNAL */){
  return new F(function(){return _1AI/* DiagramDecorator.tinkerDiagSvgExpert2 */(_/* EXTERNAL */);});
},
_1AM/* tinkerDiagSvgInvestigator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_investigator"));
}),
_1AN/* tinkerDiagSvgInvestigator2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tD/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, _1AM/* DiagramDecorator.tinkerDiagSvgInvestigator3 */, _/* EXTERNAL */);});
},
_1AO/* tinkerDiagSvgInvestigator1 */ = function(_1AP/* seP8 */, _/* EXTERNAL */){
  return new F(function(){return _1AN/* DiagramDecorator.tinkerDiagSvgInvestigator2 */(_/* EXTERNAL */);});
},
_1AQ/* tinkerDiagSvgManager3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_manager"));
}),
_1AR/* tinkerDiagSvgManager2 */ = function(_/* EXTERNAL */){
  var _1AS/* seQw */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tE/* DiagramDecorator.tinkerDiagSvgManager4 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1AT/* seQz */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1AU/* seQC */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1AV/* seQF */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tA/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1AW/* seQI */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tz/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ty/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1AQ/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */);});
},
_1AX/* tinkerDiagSvgManager1 */ = function(_1AY/* seQL */, _/* EXTERNAL */){
  return new F(function(){return _1AR/* DiagramDecorator.tinkerDiagSvgManager2 */(_/* EXTERNAL */);});
},
_1AZ/* tinkerDiagSvgPrimary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_1B0/* tinkerDiagSvgPrimary4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_1B1/* tinkerDiagSvgPrimary5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_secondary"));
}),
_1B2/* tinkerDiagSvgPrimary6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_2"));
}),
_1B3/* tinkerDiagSvgPrimary7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_primary"));
}),
_1B4/* tinkerDiagSvgPrimary2 */ = function(_/* EXTERNAL */){
  var _1B5/* sePm */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1B3/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */)),
  _1B6/* sePp */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1B2/* DiagramDecorator.tinkerDiagSvgPrimary6 */, _1B1/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1B7/* sePs */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1B0/* DiagramDecorator.tinkerDiagSvgPrimary4 */, _1B3/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1AZ/* DiagramDecorator.tinkerDiagSvgPrimary3 */, _1B3/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */);});
},
_1B8/* tinkerDiagSvgPrimary1 */ = function(_1B9/* sePv */, _/* EXTERNAL */){
  return new F(function(){return _1B4/* DiagramDecorator.tinkerDiagSvgPrimary2 */(_/* EXTERNAL */);});
},
_1Ba/* tinkerDiagSvgProducer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_producer"));
}),
_1Bb/* tinkerDiagSvgProducer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tE/* DiagramDecorator.tinkerDiagSvgManager4 */, _1Ba/* DiagramDecorator.tinkerDiagSvgProducer3 */, _/* EXTERNAL */);});
},
_1Bc/* tinkerDiagSvgProducer1 */ = function(_1Bd/* seP7 */, _/* EXTERNAL */){
  return new F(function(){return _1Bb/* DiagramDecorator.tinkerDiagSvgProducer2 */(_/* EXTERNAL */);});
},
_1Be/* tinkerDiagSvgPublic3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_public"));
}),
_1Bf/* tinkerDiagSvgPublic4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_H_3"));
}),
_1Bg/* tinkerDiagSvgPublic2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bf/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1Be/* DiagramDecorator.tinkerDiagSvgPublic3 */, _/* EXTERNAL */);});
},
_1Bh/* tinkerDiagSvgPublic1 */ = function(_1Bi/* seP6 */, _/* EXTERNAL */){
  return new F(function(){return _1Bg/* DiagramDecorator.tinkerDiagSvgPublic2 */(_/* EXTERNAL */);});
},
_1Bj/* tinkerDiagSvgRaw3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_3"));
}),
_1Bk/* tinkerDiagSvgRaw4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_1Bl/* tinkerDiagSvgRaw5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_1Bm/* tinkerDiagSvgRaw6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_raw"));
}),
_1Bn/* tinkerDiagSvgRaw2 */ = function(_/* EXTERNAL */){
  var _1Bo/* sePb */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tE/* DiagramDecorator.tinkerDiagSvgManager4 */, _1Bm/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1Bp/* sePe */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bl/* DiagramDecorator.tinkerDiagSvgRaw5 */, _1Bm/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1Bq/* sePh */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bk/* DiagramDecorator.tinkerDiagSvgRaw4 */, _1Bm/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bj/* DiagramDecorator.tinkerDiagSvgRaw3 */, _1Bm/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */);});
},
_1Br/* tinkerDiagSvgRaw1 */ = function(_1Bs/* sePk */, _/* EXTERNAL */){
  return new F(function(){return _1Bn/* DiagramDecorator.tinkerDiagSvgRaw2 */(_/* EXTERNAL */);});
},
_1Bt/* tinkerDiagSvgSecondary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_1Bu/* tinkerDiagSvgSecondary2 */ = function(_/* EXTERNAL */){
  var _1Bv/* sePx */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tx/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1B1/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1Bw/* sePA */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1B1/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1Bx/* sePD */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bf/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1B1/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1Bt/* DiagramDecorator.tinkerDiagSvgSecondary3 */, _1B1/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */);});
},
_1By/* tinkerDiagSvgSecondary1 */ = function(_1Bz/* sePG */, _/* EXTERNAL */){
  return new F(function(){return _1Bu/* DiagramDecorator.tinkerDiagSvgSecondary2 */(_/* EXTERNAL */);});
},
_1BA/* tinkerDiagSvgSteward3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_steward"));
}),
_1BB/* tinkerDiagSvgSteward2 */ = function(_/* EXTERNAL */){
  var _1BC/* seQc */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tE/* DiagramDecorator.tinkerDiagSvgManager4 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1BD/* seQf */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tC/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1BE/* seQi */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tx/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1BF/* seQl */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tB/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1BG/* seQo */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tA/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1BH/* seQr */ = B(_1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1tz/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */));
  return new F(function(){return _1sy/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ty/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1BA/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */);});
},
_1BI/* tinkerDiagSvgSteward1 */ = function(_1BJ/* seQu */, _/* EXTERNAL */){
  return new F(function(){return _1BB/* DiagramDecorator.tinkerDiagSvgSteward2 */(_/* EXTERNAL */);});
},
_1BK/* main1 */ = function(_/* EXTERNAL */){
  var _1BL/* sqiv */ = function(_/* EXTERNAL */){
    var _1BM/* sqdf */ = function(_1BN/* sqd0 */, _/* EXTERNAL */){
      return new F(function(){return _1Ab/* Overlay.overlay1 */(new T(function(){
        var _1BO/* sqd5 */ = String/* EXTERNAL */(E(_1BN/* sqd0 */));
        return fromJSStr/* EXTERNAL */(_1BO/* sqd5 */);
      }), _/* EXTERNAL */);});
    },
    _1BP/* sqdj */ = __createJSFunc/* EXTERNAL */(2, E(_1BM/* sqdf */)),
    _1BQ/* sqdo */ = "(function(s,f){Haste[s] = f;})",
    _1BR/* sqds */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1BS/* sqdA */ = __app2/* EXTERNAL */(E(_1BR/* sqds */), "overlay", _1BP/* sqdj */),
    _1BT/* sqdR */ = __createJSFunc/* EXTERNAL */(2, function(_1BU/* sqdI */, _/* EXTERNAL */){
      var _1BV/* sqdK */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_1yK/* Page.visionTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1BW/* sqdV */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1BX/* sqe3 */ = __app2/* EXTERNAL */(E(_1BW/* sqdV */), "toVision", _1BT/* sqdR */),
    _1BY/* sqek */ = __createJSFunc/* EXTERNAL */(2, function(_1BZ/* sqeb */, _/* EXTERNAL */){
      var _1C0/* sqed */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_2N/* Page.actionTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1C1/* sqeo */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1C2/* sqew */ = __app2/* EXTERNAL */(E(_1C1/* sqeo */), "toAction", _1BY/* sqek */),
    _1C3/* sqeN */ = __createJSFunc/* EXTERNAL */(2, function(_1C4/* sqeE */, _/* EXTERNAL */){
      var _1C5/* sqeG */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_3Z/* Page.lifecycleTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1C6/* sqeR */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1C7/* sqeZ */ = __app2/* EXTERNAL */(E(_1C6/* sqeR */), "toLifecycle", _1C3/* sqeN */),
    _1C8/* sqfg */ = __createJSFunc/* EXTERNAL */(2, function(_1C9/* sqf7 */, _/* EXTERNAL */){
      var _1Ca/* sqf9 */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_3R/* Page.dataTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1Cb/* sqfk */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1Cc/* sqfs */ = __app2/* EXTERNAL */(E(_1Cb/* sqfk */), "toData", _1C8/* sqfg */),
    _1Cd/* sqfJ */ = __createJSFunc/* EXTERNAL */(2, function(_1Ce/* sqfA */, _/* EXTERNAL */){
      var _1Cf/* sqfC */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_1yA/* Page.rolesTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1Cg/* sqfN */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1Ch/* sqfV */ = __app2/* EXTERNAL */(E(_1Cg/* sqfN */), "toRoles", _1Cd/* sqfJ */),
    _1Ci/* sqgc */ = __createJSFunc/* EXTERNAL */(2, function(_1Cj/* sqg3 */, _/* EXTERNAL */){
      var _1Ck/* sqg5 */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_1ym/* Page.mQuestionnaireTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1Cl/* sqgg */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1Cm/* sqgo */ = __app2/* EXTERNAL */(E(_1Cl/* sqgg */), "toMQuestionnaire", _1Ci/* sqgc */),
    _1Cn/* sqgF */ = __createJSFunc/* EXTERNAL */(2, function(_1Co/* sqgw */, _/* EXTERNAL */){
      var _1Cp/* sqgy */ = B(_JG/* FormEngine.FormElement.Tabs.toTab1 */(_1ys/* Page.tQuestionnaireTab */, _1yL/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1Cq/* sqgJ */ = eval/* EXTERNAL */(_1BQ/* sqdo */),
    _1Cr/* sqgR */ = __app2/* EXTERNAL */(E(_1Cq/* sqgJ */), "toTQuestionnaire", _1Cn/* sqgF */),
    _1Cs/* sqgU */ = B(_56/* FormEngine.JQuery.select1 */(_1zN/* Main.lvl26 */, _/* EXTERNAL */)),
    _1Ct/* sqgX */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1Br/* DiagramDecorator.tinkerDiagSvgRaw1 */, _1Cs/* sqgU */, _/* EXTERNAL */)),
    _1Cu/* sqh0 */ = B(_56/* FormEngine.JQuery.select1 */(_1zM/* Main.lvl25 */, _/* EXTERNAL */)),
    _1Cv/* sqh3 */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1B8/* DiagramDecorator.tinkerDiagSvgPrimary1 */, _1Cu/* sqh0 */, _/* EXTERNAL */)),
    _1Cw/* sqh6 */ = B(_56/* FormEngine.JQuery.select1 */(_1zL/* Main.lvl24 */, _/* EXTERNAL */)),
    _1Cx/* sqh9 */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1By/* DiagramDecorator.tinkerDiagSvgSecondary1 */, _1Cw/* sqh6 */, _/* EXTERNAL */)),
    _1Cy/* sqhc */ = B(_56/* FormEngine.JQuery.select1 */(_1zK/* Main.lvl23 */, _/* EXTERNAL */)),
    _1Cz/* sqhf */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1Bh/* DiagramDecorator.tinkerDiagSvgPublic1 */, _1Cy/* sqhc */, _/* EXTERNAL */)),
    _1CA/* sqhi */ = B(_56/* FormEngine.JQuery.select1 */(_1zJ/* Main.lvl22 */, _/* EXTERNAL */)),
    _1CB/* sqhl */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1Bc/* DiagramDecorator.tinkerDiagSvgProducer1 */, _1CA/* sqhi */, _/* EXTERNAL */)),
    _1CC/* sqho */ = B(_56/* FormEngine.JQuery.select1 */(_1zI/* Main.lvl21 */, _/* EXTERNAL */)),
    _1CD/* sqhr */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1AK/* DiagramDecorator.tinkerDiagSvgExpert1 */, _1CC/* sqho */, _/* EXTERNAL */)),
    _1CE/* sqhu */ = B(_56/* FormEngine.JQuery.select1 */(_1zH/* Main.lvl20 */, _/* EXTERNAL */)),
    _1CF/* sqhx */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1Aq/* DiagramDecorator.tinkerDiagSvgConsumer1 */, _1CE/* sqhu */, _/* EXTERNAL */)),
    _1CG/* sqhA */ = B(_56/* FormEngine.JQuery.select1 */(_1zG/* Main.lvl19 */, _/* EXTERNAL */)),
    _1CH/* sqhD */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1Az/* DiagramDecorator.tinkerDiagSvgCurator1 */, _1CG/* sqhA */, _/* EXTERNAL */)),
    _1CI/* sqhG */ = B(_56/* FormEngine.JQuery.select1 */(_1zF/* Main.lvl18 */, _/* EXTERNAL */)),
    _1CJ/* sqhJ */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1AF/* DiagramDecorator.tinkerDiagSvgCustodian1 */, _1CI/* sqhG */, _/* EXTERNAL */)),
    _1CK/* sqhM */ = B(_56/* FormEngine.JQuery.select1 */(_1zE/* Main.lvl17 */, _/* EXTERNAL */)),
    _1CL/* sqhP */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1BI/* DiagramDecorator.tinkerDiagSvgSteward1 */, _1CK/* sqhM */, _/* EXTERNAL */)),
    _1CM/* sqhS */ = B(_56/* FormEngine.JQuery.select1 */(_1zD/* Main.lvl16 */, _/* EXTERNAL */)),
    _1CN/* sqhV */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1AX/* DiagramDecorator.tinkerDiagSvgManager1 */, _1CM/* sqhS */, _/* EXTERNAL */)),
    _1CO/* sqhY */ = B(_56/* FormEngine.JQuery.select1 */(_1zC/* Main.lvl15 */, _/* EXTERNAL */)),
    _1CP/* sqi1 */ = B(_L7/* FormEngine.JQuery.onLoad1 */(_1AO/* DiagramDecorator.tinkerDiagSvgInvestigator1 */, _1CO/* sqhY */, _/* EXTERNAL */)),
    _1CQ/* sqi4 */ = B(_56/* FormEngine.JQuery.select1 */(_3T/* Main.getRespondentKey2 */, _/* EXTERNAL */)),
    _1CR/* sqic */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_1CQ/* sqi4 */)),
    _1CS/* sqis */ = B(A(_3j/* Haste.Ajax.ajaxRequest */,[_2E/* Control.Monad.IO.Class.$fMonadIOIO */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _d/* Haste.Prim.JSType.$fJSType[] */, _2F/* Haste.Ajax.POST */, _40/* Main.lvl11 */, new T2(1,new T2(0,_41/* Main.lvl12 */,new T(function(){
      var _1CT/* sqig */ = String/* EXTERNAL */(_1CR/* sqic */);
      return toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_1CT/* sqig */));
    })),_I/* GHC.Types.[] */), _1zc/* Main.lvl14 */, _/* EXTERNAL */]));
    return _3e/* Haste.Prim.Any.jsNull */;
  },
  _1CU/* sqiz */ = __createJSFunc/* EXTERNAL */(0, E(_1BL/* sqiv */)),
  _1CV/* sqiF */ = __app1/* EXTERNAL */(E(_1An/* FormEngine.JQuery.ready_f1 */), _1CU/* sqiz */);
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1CW/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1BK/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1CW, [0]));};window.onload = hasteMain;