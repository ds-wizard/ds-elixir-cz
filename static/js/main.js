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
_2M/* pageTabGroup33 */ = new T2(6,_2L/* Page.pageTabGroup34 */,_I/* GHC.Types.[] */),
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
_3Q/* pageTabGroup23 */ = new T2(6,_3P/* Page.pageTabGroup24 */,_I/* GHC.Types.[] */),
_3R/* dataTab */ = new T3(0,_3Q/* Page.pageTabGroup23 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_3S/* getRadioValue_f1 */ = new T(function(){
  return (function (jq) { return jq.val(); });
}),
_3T/* getRespondentKey2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#respondent_key_field"));
}),
_3U/* pageTabGroup32 */ = 300,
_3V/* pageTabGroup31 */ = new T2(1,_3U/* Page.pageTabGroup32 */,_I/* GHC.Types.[] */),
_3W/* pageTabGroup30 */ = new T2(1,_3V/* Page.pageTabGroup31 */,_2H/* Page.pageTabGroup10 */),
_3X/* pageTabGroup29 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_3W/* Page.pageTabGroup30 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_3Y/* pageTabGroup28 */ = new T2(6,_3X/* Page.pageTabGroup29 */,_I/* GHC.Types.[] */),
_3Z/* lifecycleTab */ = new T3(0,_3Y/* Page.pageTabGroup28 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_40/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("api/getData"));
}),
_41/* lvl13 */ = "respondent_key",
_42/* appearJq5 */ = "(function (key, val, jq) { jq.css(key, val); return jq; })",
_43/* $wa2 */ = function(_44/* so3v */, _45/* so3w */, _46/* so3x */, _/* EXTERNAL */){
  var _47/* so3M */ = eval/* EXTERNAL */(E(_42/* FormEngine.JQuery.appearJq5 */));
  return new F(function(){return E(_47/* so3M */)(toJSStr/* EXTERNAL */(E(_44/* so3v */)), toJSStr/* EXTERNAL */(E(_45/* so3w */)), _46/* so3x */);});
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
_4k/* $wtoPx */ = function(_4l/* snzE */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(0, _4l/* snzE */, _I/* GHC.Types.[] */)), _4j/* FormEngine.JQuery.toPx1 */);});
},
_4m/* descSubpaneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane"));
}),
_4n/* elemChapter */ = function(_4o/* s5YA */){
  while(1){
    var _4p/* s5YB */ = E(_4o/* s5YA */);
    switch(_4p/* s5YB */._){
      case 0:
        return E(_4p/* s5YB */);
      case 1:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 2:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 3:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 4:
        _4o/* s5YA */ = _4p/* s5YB */.d;
        continue;
      case 5:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 6:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 7:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 8:
        _4o/* s5YA */ = _4p/* s5YB */.d;
        continue;
      case 9:
        _4o/* s5YA */ = _4p/* s5YB */.c;
        continue;
      case 10:
        _4o/* s5YA */ = _4p/* s5YB */.b;
        continue;
      default:
        _4o/* s5YA */ = _4p/* s5YB */.b;
        continue;
    }
  }
},
_4q/* fiDescriptor */ = function(_4r/* s7y3 */){
  var _4s/* s7y4 */ = E(_4r/* s7y3 */);
  switch(_4s/* s7y4 */._){
    case 0:
      return E(_4s/* s7y4 */.a);
    case 1:
      return E(_4s/* s7y4 */.a);
    case 2:
      return E(_4s/* s7y4 */.a);
    case 3:
      return E(_4s/* s7y4 */.a);
    case 4:
      return E(_4s/* s7y4 */.a);
    case 5:
      return E(_4s/* s7y4 */.a);
    case 6:
      return E(_4s/* s7y4 */.a);
    case 7:
      return E(_4s/* s7y4 */.a);
    case 8:
      return E(_4s/* s7y4 */.a);
    case 9:
      return E(_4s/* s7y4 */.a);
    case 10:
      return E(_4s/* s7y4 */.a);
    default:
      return E(_4s/* s7y4 */.a);
  }
},
_4t/* formItem */ = function(_4u/* s5Qy */){
  var _4v/* s5Qz */ = E(_4u/* s5Qy */);
  switch(_4v/* s5Qz */._){
    case 0:
      return E(_4v/* s5Qz */.a);
    case 1:
      return E(_4v/* s5Qz */.a);
    case 2:
      return E(_4v/* s5Qz */.a);
    case 3:
      return E(_4v/* s5Qz */.a);
    case 4:
      return E(_4v/* s5Qz */.a);
    case 5:
      return E(_4v/* s5Qz */.a);
    case 6:
      return E(_4v/* s5Qz */.a);
    case 7:
      return E(_4v/* s5Qz */.a);
    case 8:
      return E(_4v/* s5Qz */.a);
    case 9:
      return E(_4v/* s5Qz */.a);
    case 10:
      return E(_4v/* s5Qz */.a);
    default:
      return E(_4v/* s5Qz */.a);
  }
},
_4w/* $fShowInt_$cshow */ = function(_4x/* sffD */){
  return new F(function(){return _4e/* GHC.Show.$wshowSignedInt */(0, E(_4x/* sffD */), _I/* GHC.Types.[] */);});
},
_4y/* $wgo */ = function(_4z/* s7xh */, _4A/* s7xi */){
  var _4B/* s7xj */ = E(_4z/* s7xh */);
  if(!_4B/* s7xj */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4C/* s7xk */ = _4B/* s7xj */.a,
    _4D/* s7xm */ = E(_4A/* s7xi */);
    return (_4D/* s7xm */==1) ? new T2(1,new T(function(){
      return B(_4w/* GHC.Show.$fShowInt_$cshow */(_4C/* s7xk */));
    }),_I/* GHC.Types.[] */) : new T2(1,new T(function(){
      return B(_4w/* GHC.Show.$fShowInt_$cshow */(_4C/* s7xk */));
    }),new T(function(){
      return B(_4y/* FormEngine.FormItem.$wgo */(_4B/* s7xj */.b, _4D/* s7xm */-1|0));
    }));
  }
},
_4E/* intercalate1 */ = function(_4F/* s1WJa */){
  var _4G/* s1WJb */ = E(_4F/* s1WJa */);
  if(!_4G/* s1WJb */._){
    return __Z/* EXTERNAL */;
  }else{
    return new F(function(){return _12/* GHC.Base.++ */(_4G/* s1WJb */.a, new T(function(){
      return B(_4E/* Data.OldList.intercalate1 */(_4G/* s1WJb */.b));
    },1));});
  }
},
_4H/* numbering2text1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_4I/* prependToAll */ = function(_4J/* s1WIX */, _4K/* s1WIY */){
  var _4L/* s1WIZ */ = E(_4K/* s1WIY */);
  return (_4L/* s1WIZ */._==0) ? __Z/* EXTERNAL */ : new T2(1,_4J/* s1WIX */,new T2(1,_4L/* s1WIZ */.a,new T(function(){
    return B(_4I/* Data.OldList.prependToAll */(_4J/* s1WIX */, _4L/* s1WIZ */.b));
  })));
},
_4M/* numbering2text */ = function(_4N/* s7xr */){
  var _4O/* s7xs */ = E(_4N/* s7xr */);
  if(!_4O/* s7xs */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4P/* s7xx */ = E(_4O/* s7xs */.b)+1|0;
    if(0>=_4P/* s7xx */){
      return __Z/* EXTERNAL */;
    }else{
      var _4Q/* s7xA */ = B(_4y/* FormEngine.FormItem.$wgo */(_4O/* s7xs */.a, _4P/* s7xx */));
      if(!_4Q/* s7xA */._){
        return __Z/* EXTERNAL */;
      }else{
        return new F(function(){return _4E/* Data.OldList.intercalate1 */(new T2(1,_4Q/* s7xA */.a,new T(function(){
          return B(_4I/* Data.OldList.prependToAll */(_4H/* FormEngine.FormItem.numbering2text1 */, _4Q/* s7xA */.b));
        })));});
      }
    }
  }
},
_4R/* descSubpaneId */ = function(_4S/* stoE */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_4S/* stoE */)))))).b)), _4m/* FormEngine.FormElement.Identifiers.descSubpaneId1 */);});
},
_4T/* getScrollTop_f1 */ = new T(function(){
  return (function (jq) { return jq.scrollTop(); });
}),
_4U/* getTop_f1 */ = new T(function(){
  return (function (jq) { return jq.position().top; });
}),
_4V/* getWindow_f1 */ = new T(function(){
  return (function () { return $(window); });
}),
_4W/* isVisible_f1 */ = new T(function(){
  return (function (jq) { return jq.is(':visible'); });
}),
_4X/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_4Y/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_4Z/* select2 */ = "(function (elId) { var res = $(elId); if (res.length === 0) { console.warn(\'empty $ selection \' + elId); }; return res; })",
_50/* select1 */ = function(_51/* snVJ */, _/* EXTERNAL */){
  var _52/* snVT */ = eval/* EXTERNAL */(E(_4Z/* FormEngine.JQuery.select2 */));
  return new F(function(){return E(_52/* snVT */)(toJSStr/* EXTERNAL */(E(_51/* snVJ */)));});
},
_53/* $wa1 */ = function(_54/* sNCw */, _/* EXTERNAL */){
  var _55/* sNCy */ = E(_54/* sNCw */);
  if(!_55/* sNCy */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _56/* sNCB */ = B(_12/* GHC.Base.++ */(_4Y/* Main.lvl9 */, new T(function(){
      return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneId */(_55/* sNCy */.a));
    },1))),
    _57/* sNCD */ = B(_50/* FormEngine.JQuery.select1 */(_56/* sNCB */, _/* EXTERNAL */)),
    _58/* sNCI */ = E(_4W/* FormEngine.JQuery.isVisible_f1 */),
    _59/* sNCL */ = _58/* sNCI */(E(_57/* sNCD */)),
    _5a/* sNCO */ = function(_5b/* sNCP */, _/* EXTERNAL */){
      var _5c/* sNCR */ = E(_5b/* sNCP */);
      if(!_5c/* sNCR */._){
        return _I/* GHC.Types.[] */;
      }else{
        var _5d/* sNCU */ = B(_12/* GHC.Base.++ */(_4Y/* Main.lvl9 */, new T(function(){
          return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneId */(_5c/* sNCR */.a));
        },1))),
        _5e/* sNCW */ = B(_50/* FormEngine.JQuery.select1 */(_5d/* sNCU */, _/* EXTERNAL */)),
        _5f/* sND2 */ = _58/* sNCI */(E(_5e/* sNCW */)),
        _5g/* sND5 */ = B(_5a/* sNCO */(_5c/* sNCR */.b, _/* EXTERNAL */));
        return new T(function(){
          if(!_5f/* sND2 */){
            return E(_5g/* sND5 */);
          }else{
            return new T2(1,_5d/* sNCU */,_5g/* sND5 */);
          }
        });
      }
    },
    _5h/* sNDa */ = B(_5a/* sNCO */(_55/* sNCy */.b, _/* EXTERNAL */)),
    _5i/* sNDd */ = function(_5j/* sNDe */, _5k/* sNDf */){
      var _5l/* sNDg */ = B(_50/* FormEngine.JQuery.select1 */(_5j/* sNDe */, _/* EXTERNAL */)),
      _5m/* sNDm */ = E(_4V/* FormEngine.JQuery.getWindow_f1 */)(),
      _5n/* sNDs */ = E(_4T/* FormEngine.JQuery.getScrollTop_f1 */)(_5m/* sNDm */),
      _5o/* sNDv */ = E(_5l/* sNDg */),
      _5p/* sNDA */ = E(_4U/* FormEngine.JQuery.getTop_f1 */)(_5o/* sNDv */),
      _5q/* sNDE */ = Number/* EXTERNAL */(_5n/* sNDs */),
      _5r/* sNDI */ = jsTrunc/* EXTERNAL */(_5q/* sNDE */),
      _5s/* sNDM */ = Number/* EXTERNAL */(_5p/* sNDA */),
      _5t/* sNDQ */ = jsTrunc/* EXTERNAL */(_5s/* sNDM */),
      _5u/* sNDT */ = _5r/* sNDI */-_5t/* sNDQ */|0;
      if(_5u/* sNDT */<=0){
        return _0/* GHC.Tuple.() */;
      }else{
        var _5v/* sNDX */ = B(_43/* FormEngine.JQuery.$wa2 */(_4X/* Main.lvl10 */, B(_4k/* FormEngine.JQuery.$wtoPx */(_5u/* sNDT */)), _5o/* sNDv */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      }
    };
    if(!_59/* sNCL */){
      var _5w/* sNE1 */ = E(_5h/* sNDa */);
      if(!_5w/* sNE1 */._){
        return _0/* GHC.Tuple.() */;
      }else{
        return new F(function(){return _5i/* sNDd */(_5w/* sNE1 */.a, _5w/* sNE1 */.b);});
      }
    }else{
      return new F(function(){return _5i/* sNDd */(_56/* sNCB */, _5h/* sNDa */);});
    }
  }
},
_5x/* resize2 */ = "(function (jq) { jq.resize(); })",
_5y/* $wa17 */ = function(_5z/* snBP */, _/* EXTERNAL */){
  var _5A/* snBU */ = eval/* EXTERNAL */(E(_5x/* FormEngine.JQuery.resize2 */)),
  _5B/* snC2 */ = E(_5A/* snBU */)(_5z/* snBP */);
  return _5z/* snBP */;
},
_5C/* catMaybes1 */ = function(_5D/*  s7rA */){
  while(1){
    var _5E/*  catMaybes1 */ = B((function(_5F/* s7rA */){
      var _5G/* s7rB */ = E(_5F/* s7rA */);
      if(!_5G/* s7rB */._){
        return __Z/* EXTERNAL */;
      }else{
        var _5H/* s7rD */ = _5G/* s7rB */.b,
        _5I/* s7rE */ = E(_5G/* s7rB */.a);
        if(!_5I/* s7rE */._){
          _5D/*  s7rA */ = _5H/* s7rD */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_5I/* s7rE */.a,new T(function(){
            return B(_5C/* Data.Maybe.catMaybes1 */(_5H/* s7rD */));
          }));
        }
      }
    })(_5D/*  s7rA */));
    if(_5E/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _5E/*  catMaybes1 */;
    }
  }
},
_5J/* errorIO2 */ = "(function (s) { console.error(s); })",
_5K/* errorIO1 */ = function(_5L/* snKt */, _/* EXTERNAL */){
  var _5M/* snKD */ = eval/* EXTERNAL */(E(_5J/* FormEngine.JQuery.errorIO2 */)),
  _5N/* snKL */ = E(_5M/* snKD */)(toJSStr/* EXTERNAL */(E(_5L/* snKt */)));
  return _0/* GHC.Tuple.() */;
},
_5O/* $fShowNumbering2 */ = 0,
_5P/* $wgo2 */ = function(_5Q/*  s7rx */, _5R/*  s7ry */, _5S/*  s7rz */){
  while(1){
    var _5T/*  $wgo2 */ = B((function(_5U/* s7rx */, _5V/* s7ry */, _5W/* s7rz */){
      var _5X/* s7rA */ = E(_5U/* s7rx */);
      if(!_5X/* s7rA */._){
        return new T2(0,_5V/* s7ry */,_5W/* s7rz */);
      }else{
        var _5Y/* s7rB */ = _5X/* s7rA */.a,
        _5Z/* s7rM */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_5W/* s7rz */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_5V/* s7ry */, _5Y/* s7rB */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _5Q/*  s7rx */ = _5X/* s7rA */.b;
        _5R/*  s7ry */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_5V/* s7ry */, _5Y/* s7rB */)).a);
        });
        _5S/*  s7rz */ = _5Z/* s7rM */;
        return __continue/* EXTERNAL */;
      }
    })(_5Q/*  s7rx */, _5R/*  s7ry */, _5S/*  s7rz */));
    if(_5T/*  $wgo2 */!=__continue/* EXTERNAL */){
      return _5T/*  $wgo2 */;
    }
  }
},
_61/* $wgo3 */ = function(_62/*  s7rN */, _63/*  s7rO */, _64/*  s7rP */){
  while(1){
    var _65/*  $wgo3 */ = B((function(_66/* s7rN */, _67/* s7rO */, _68/* s7rP */){
      var _69/* s7rQ */ = E(_66/* s7rN */);
      if(!_69/* s7rQ */._){
        return new T2(0,_67/* s7rO */,_68/* s7rP */);
      }else{
        var _6a/* s7rR */ = _69/* s7rQ */.a,
        _6b/* s7s2 */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_68/* s7rP */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_67/* s7rO */, _6a/* s7rR */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _62/*  s7rN */ = _69/* s7rQ */.b;
        _63/*  s7rO */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_67/* s7rO */, _6a/* s7rR */)).a);
        });
        _64/*  s7rP */ = _6b/* s7s2 */;
        return __continue/* EXTERNAL */;
      }
    })(_62/*  s7rN */, _63/*  s7rO */, _64/*  s7rP */));
    if(_65/*  $wgo3 */!=__continue/* EXTERNAL */){
      return _65/*  $wgo3 */;
    }
  }
},
_6c/* $wgo4 */ = function(_6d/*  s7s3 */, _6e/*  s7s4 */, _6f/*  s7s5 */){
  while(1){
    var _6g/*  $wgo4 */ = B((function(_6h/* s7s3 */, _6i/* s7s4 */, _6j/* s7s5 */){
      var _6k/* s7s6 */ = E(_6h/* s7s3 */);
      if(!_6k/* s7s6 */._){
        return new T2(0,_6i/* s7s4 */,_6j/* s7s5 */);
      }else{
        var _6l/* s7s7 */ = _6k/* s7s6 */.a,
        _6m/* s7si */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6j/* s7s5 */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6i/* s7s4 */, _6l/* s7s7 */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6d/*  s7s3 */ = _6k/* s7s6 */.b;
        _6e/*  s7s4 */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6i/* s7s4 */, _6l/* s7s7 */)).a);
        });
        _6f/*  s7s5 */ = _6m/* s7si */;
        return __continue/* EXTERNAL */;
      }
    })(_6d/*  s7s3 */, _6e/*  s7s4 */, _6f/*  s7s5 */));
    if(_6g/*  $wgo4 */!=__continue/* EXTERNAL */){
      return _6g/*  $wgo4 */;
    }
  }
},
_6n/* $wgo5 */ = function(_6o/*  s7sj */, _6p/*  s7sk */, _6q/*  s7sl */){
  while(1){
    var _6r/*  $wgo5 */ = B((function(_6s/* s7sj */, _6t/* s7sk */, _6u/* s7sl */){
      var _6v/* s7sm */ = E(_6s/* s7sj */);
      if(!_6v/* s7sm */._){
        return new T2(0,_6t/* s7sk */,_6u/* s7sl */);
      }else{
        var _6w/* s7sn */ = _6v/* s7sm */.a,
        _6x/* s7sy */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6u/* s7sl */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6t/* s7sk */, _6w/* s7sn */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6o/*  s7sj */ = _6v/* s7sm */.b;
        _6p/*  s7sk */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6t/* s7sk */, _6w/* s7sn */)).a);
        });
        _6q/*  s7sl */ = _6x/* s7sy */;
        return __continue/* EXTERNAL */;
      }
    })(_6o/*  s7sj */, _6p/*  s7sk */, _6q/*  s7sl */));
    if(_6r/*  $wgo5 */!=__continue/* EXTERNAL */){
      return _6r/*  $wgo5 */;
    }
  }
},
_6y/* $wgo6 */ = function(_6z/*  s7sz */, _6A/*  s7sA */, _6B/*  s7sB */){
  while(1){
    var _6C/*  $wgo6 */ = B((function(_6D/* s7sz */, _6E/* s7sA */, _6F/* s7sB */){
      var _6G/* s7sC */ = E(_6D/* s7sz */);
      if(!_6G/* s7sC */._){
        return new T2(0,_6E/* s7sA */,_6F/* s7sB */);
      }else{
        var _6H/* s7sD */ = _6G/* s7sC */.a,
        _6I/* s7sO */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_6F/* s7sB */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6E/* s7sA */, _6H/* s7sD */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _6z/*  s7sz */ = _6G/* s7sC */.b;
        _6A/*  s7sA */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_6E/* s7sA */, _6H/* s7sD */)).a);
        });
        _6B/*  s7sB */ = _6I/* s7sO */;
        return __continue/* EXTERNAL */;
      }
    })(_6z/*  s7sz */, _6A/*  s7sA */, _6B/*  s7sB */));
    if(_6C/*  $wgo6 */!=__continue/* EXTERNAL */){
      return _6C/*  $wgo6 */;
    }
  }
},
_6J/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_6K/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_6L/* lvl2 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_6K/* GHC.List.prel_list_str */, _6J/* GHC.List.lvl1 */));
}),
_6M/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_6L/* GHC.List.lvl2 */));
}),
_6N/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_6O/* lvl4 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_6K/* GHC.List.prel_list_str */, _6N/* GHC.List.lvl3 */));
}),
_6P/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_6O/* GHC.List.lvl4 */));
}),
_6Q/* poly_$wgo2 */ = function(_6R/* s9uh */, _6S/* s9ui */){
  while(1){
    var _6T/* s9uj */ = E(_6R/* s9uh */);
    if(!_6T/* s9uj */._){
      return E(_6P/* GHC.List.!!1 */);
    }else{
      var _6U/* s9um */ = E(_6S/* s9ui */);
      if(!_6U/* s9um */){
        return E(_6T/* s9uj */.a);
      }else{
        _6R/* s9uh */ = _6T/* s9uj */.b;
        _6S/* s9ui */ = _6U/* s9um */-1|0;
        continue;
      }
    }
  }
},
_6V/* $w!! */ = function(_6W/* s9uo */, _6X/* s9up */){
  if(_6X/* s9up */>=0){
    return new F(function(){return _6Q/* GHC.List.poly_$wgo2 */(_6W/* s9uo */, _6X/* s9up */);});
  }else{
    return E(_6M/* GHC.List.negIndex */);
  }
},
_6Y/* xs */ = new T(function(){
  return new T2(1,_5O/* FormEngine.FormItem.$fShowNumbering2 */,_6Y/* FormEngine.FormItem.xs */);
}),
_6Z/* incrementAtLevel */ = function(_70/* s7ra */){
  var _71/* s7rb */ = E(_70/* s7ra */);
  if(!_71/* s7rb */._){
    return __Z/* EXTERNAL */;
  }else{
    var _72/* s7rc */ = _71/* s7rb */.a,
    _73/* s7rd */ = _71/* s7rb */.b,
    _74/* s7rw */ = new T(function(){
      var _75/* s7re */ = E(_73/* s7rd */),
      _76/* s7rk */ = new T2(1,new T(function(){
        return B(_6V/* GHC.List.$w!! */(_72/* s7rc */, _75/* s7re */))+1|0;
      }),_6Y/* FormEngine.FormItem.xs */);
      if(0>=_75/* s7re */){
        return E(_76/* s7rk */);
      }else{
        var _77/* s7rn */ = function(_78/* s7ro */, _79/* s7rp */){
          var _7a/* s7rq */ = E(_78/* s7ro */);
          if(!_7a/* s7rq */._){
            return E(_76/* s7rk */);
          }else{
            var _7b/* s7rr */ = _7a/* s7rq */.a,
            _7c/* s7rt */ = E(_79/* s7rp */);
            return (_7c/* s7rt */==1) ? new T2(1,_7b/* s7rr */,_76/* s7rk */) : new T2(1,_7b/* s7rr */,new T(function(){
              return B(_77/* s7rn */(_7a/* s7rq */.b, _7c/* s7rt */-1|0));
            }));
          }
        };
        return B(_77/* s7rn */(_72/* s7rc */, _75/* s7re */));
      }
    });
    return new T2(1,_74/* s7rw */,_73/* s7rd */);
  }
},
_7d/* $wgo7 */ = function(_7e/*  s7sP */, _7f/*  s7sQ */, _7g/*  s7sR */){
  while(1){
    var _7h/*  $wgo7 */ = B((function(_7i/* s7sP */, _7j/* s7sQ */, _7k/* s7sR */){
      var _7l/* s7sS */ = E(_7i/* s7sP */);
      if(!_7l/* s7sS */._){
        return new T2(0,_7j/* s7sQ */,_7k/* s7sR */);
      }else{
        var _7m/* s7sU */ = _7l/* s7sS */.b,
        _7n/* s7sV */ = E(_7l/* s7sS */.a);
        if(!_7n/* s7sV */._){
          var _7o/*   s7sQ */ = _7j/* s7sQ */;
          _7e/*  s7sP */ = _7m/* s7sU */;
          _7f/*  s7sQ */ = _7o/*   s7sQ */;
          _7g/*  s7sR */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_7k/* s7sR */, new T2(1,_7n/* s7sV */,_I/* GHC.Types.[] */)));
          });
          return __continue/* EXTERNAL */;
        }else{
          var _7p/* s7th */ = new T(function(){
            var _7q/* s7te */ = new T(function(){
              var _7r/* s7ta */ = new T(function(){
                var _7s/* s7t3 */ = E(_7j/* s7sQ */);
                if(!_7s/* s7t3 */._){
                  return __Z/* EXTERNAL */;
                }else{
                  return new T2(1,_7s/* s7t3 */.a,new T(function(){
                    return E(_7s/* s7t3 */.b)+1|0;
                  }));
                }
              });
              return E(B(_6y/* FormEngine.FormItem.$wgo6 */(_7n/* s7sV */.c, _7r/* s7ta */, _I/* GHC.Types.[] */)).b);
            });
            return B(_12/* GHC.Base.++ */(_7k/* s7sR */, new T2(1,new T3(1,_7j/* s7sQ */,_7n/* s7sV */.b,_7q/* s7te */),_I/* GHC.Types.[] */)));
          });
          _7e/*  s7sP */ = _7m/* s7sU */;
          _7f/*  s7sQ */ = new T(function(){
            return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7j/* s7sQ */));
          });
          _7g/*  s7sR */ = _7p/* s7th */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_7e/*  s7sP */, _7f/*  s7sQ */, _7g/*  s7sR */));
    if(_7h/*  $wgo7 */!=__continue/* EXTERNAL */){
      return _7h/*  $wgo7 */;
    }
  }
},
_60/* $wincrementNumbering */ = function(_7t/* s7ti */, _7u/* s7tj */){
  var _7v/* s7tk */ = E(_7u/* s7tj */);
  switch(_7v/* s7tk */._){
    case 0:
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T1(0,new T(function(){
        var _7w/* s7tn */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7w/* s7tn */.a,b:_7t/* s7ti */,c:_7w/* s7tn */.c,d:_7w/* s7tn */.d,e:_7w/* s7tn */.e,f:_7w/* s7tn */.f,g:_7w/* s7tn */.g,h:_7w/* s7tn */.h,i:_7w/* s7tn */.i};
      })));
    case 1:
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T1(1,new T(function(){
        var _7x/* s7tB */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7x/* s7tB */.a,b:_7t/* s7ti */,c:_7x/* s7tB */.c,d:_7x/* s7tB */.d,e:_7x/* s7tB */.e,f:_7x/* s7tB */.f,g:_7x/* s7tB */.g,h:_7x/* s7tB */.h,i:_7x/* s7tB */.i};
      })));
    case 2:
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T1(2,new T(function(){
        var _7y/* s7tP */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7y/* s7tP */.a,b:_7t/* s7ti */,c:_7y/* s7tP */.c,d:_7y/* s7tP */.d,e:_7y/* s7tP */.e,f:_7y/* s7tP */.f,g:_7y/* s7tP */.g,h:_7y/* s7tP */.h,i:_7y/* s7tP */.i};
      })));
    case 3:
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T2(3,new T(function(){
        var _7z/* s7u4 */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7z/* s7u4 */.a,b:_7t/* s7ti */,c:_7z/* s7u4 */.c,d:_7z/* s7u4 */.d,e:_7z/* s7u4 */.e,f:_7z/* s7u4 */.f,g:_7z/* s7u4 */.g,h:_7z/* s7u4 */.h,i:_7z/* s7u4 */.i};
      }),_7v/* s7tk */.b));
    case 4:
      var _7A/* s7uF */ = new T(function(){
        var _7B/* s7uB */ = new T(function(){
          var _7C/* s7uu */ = E(_7t/* s7ti */);
          if(!_7C/* s7uu */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7C/* s7uu */.a,new T(function(){
              return E(_7C/* s7uu */.b)+1|0;
            }));
          }
        });
        return E(B(_7d/* FormEngine.FormItem.$wgo7 */(_7v/* s7tk */.b, _7B/* s7uB */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T2(4,new T(function(){
        var _7D/* s7uj */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7D/* s7uj */.a,b:_7t/* s7ti */,c:_7D/* s7uj */.c,d:_7D/* s7uj */.d,e:_7D/* s7uj */.e,f:_7D/* s7uj */.f,g:_7D/* s7uj */.g,h:_7D/* s7uj */.h,i:_7D/* s7uj */.i};
      }),_7A/* s7uF */));
    case 5:
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T2(5,new T(function(){
        var _7E/* s7uK */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7E/* s7uK */.a,b:_7t/* s7ti */,c:_7E/* s7uK */.c,d:_7E/* s7uK */.d,e:_7E/* s7uK */.e,f:_7E/* s7uK */.f,g:_7E/* s7uK */.g,h:_7E/* s7uK */.h,i:_7E/* s7uK */.i};
      }),_7v/* s7tk */.b));
    case 6:
      var _7F/* s7vl */ = new T(function(){
        var _7G/* s7vh */ = new T(function(){
          var _7H/* s7va */ = E(_7t/* s7ti */);
          if(!_7H/* s7va */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7H/* s7va */.a,new T(function(){
              return E(_7H/* s7va */.b)+1|0;
            }));
          }
        });
        return E(B(_6n/* FormEngine.FormItem.$wgo5 */(_7v/* s7tk */.b, _7G/* s7vh */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T2(6,new T(function(){
        var _7I/* s7uZ */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7I/* s7uZ */.a,b:_7t/* s7ti */,c:_7I/* s7uZ */.c,d:_7I/* s7uZ */.d,e:_7I/* s7uZ */.e,f:_7I/* s7uZ */.f,g:_7I/* s7uZ */.g,h:_7I/* s7uZ */.h,i:_7I/* s7uZ */.i};
      }),_7F/* s7vl */));
    case 7:
      var _7J/* s7vR */ = new T(function(){
        var _7K/* s7vN */ = new T(function(){
          var _7L/* s7vG */ = E(_7t/* s7ti */);
          if(!_7L/* s7vG */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7L/* s7vG */.a,new T(function(){
              return E(_7L/* s7vG */.b)+1|0;
            }));
          }
        });
        return E(B(_6c/* FormEngine.FormItem.$wgo4 */(_7v/* s7tk */.c, _7K/* s7vN */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T3(7,new T(function(){
        var _7M/* s7vr */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7M/* s7vr */.a,b:_7t/* s7ti */,c:_7M/* s7vr */.c,d:_7M/* s7vr */.d,e:_7M/* s7vr */.e,f:_7M/* s7vr */.f,g:_7M/* s7vr */.g,h:_7M/* s7vr */.h,i:_7M/* s7vr */.i};
      }),new T(function(){
        var _7N/* s7vC */ = E(_7t/* s7ti */);
        if(!_7N/* s7vC */._){
          return E(_5O/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_7N/* s7vC */.b);
        }
      }),_7J/* s7vR */));
    case 8:
      var _7O/* s7wn */ = new T(function(){
        var _7P/* s7wj */ = new T(function(){
          var _7Q/* s7wc */ = E(_7t/* s7ti */);
          if(!_7Q/* s7wc */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7Q/* s7wc */.a,new T(function(){
              return E(_7Q/* s7wc */.b)+1|0;
            }));
          }
        });
        return E(B(_61/* FormEngine.FormItem.$wgo3 */(_7v/* s7tk */.c, _7P/* s7wj */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T3(8,new T(function(){
        var _7R/* s7vX */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7R/* s7vX */.a,b:_7t/* s7ti */,c:_7R/* s7vX */.c,d:_7R/* s7vX */.d,e:_7R/* s7vX */.e,f:_7R/* s7vX */.f,g:_7R/* s7vX */.g,h:_7R/* s7vX */.h,i:_7R/* s7vX */.i};
      }),new T(function(){
        var _7S/* s7w8 */ = E(_7t/* s7ti */);
        if(!_7S/* s7w8 */._){
          return E(_5O/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_7S/* s7w8 */.b);
        }
      }),_7O/* s7wn */));
    case 9:
      var _7T/* s7wT */ = new T(function(){
        var _7U/* s7wP */ = new T(function(){
          var _7V/* s7wI */ = E(_7t/* s7ti */);
          if(!_7V/* s7wI */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_7V/* s7wI */.a,new T(function(){
              return E(_7V/* s7wI */.b)+1|0;
            }));
          }
        });
        return E(B(_5P/* FormEngine.FormItem.$wgo2 */(_7v/* s7tk */.c, _7U/* s7wP */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_6Z/* FormEngine.FormItem.incrementAtLevel */(_7t/* s7ti */));
      }),new T3(9,new T(function(){
        var _7W/* s7wt */ = E(_7v/* s7tk */.a);
        return {_:0,a:_7W/* s7wt */.a,b:_7t/* s7ti */,c:_7W/* s7wt */.c,d:_7W/* s7wt */.d,e:_7W/* s7wt */.e,f:_7W/* s7wt */.f,g:_7W/* s7wt */.g,h:_7W/* s7wt */.h,i:_7W/* s7wt */.i};
      }),new T(function(){
        var _7X/* s7wE */ = E(_7t/* s7ti */);
        if(!_7X/* s7wE */._){
          return E(_5O/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_7X/* s7wE */.b);
        }
      }),_7T/* s7wT */));
    case 10:
      return new T2(0,_7t/* s7ti */,_7v/* s7tk */);
    default:
      return new T2(0,_7t/* s7ti */,_7v/* s7tk */);
  }
},
_7Y/* $wgo1 */ = function(_7Z/*  s7wX */, _80/*  s7wY */, _81/*  s7wZ */){
  while(1){
    var _82/*  $wgo1 */ = B((function(_83/* s7wX */, _84/* s7wY */, _85/* s7wZ */){
      var _86/* s7x0 */ = E(_83/* s7wX */);
      if(!_86/* s7x0 */._){
        return new T2(0,_84/* s7wY */,_85/* s7wZ */);
      }else{
        var _87/* s7x1 */ = _86/* s7x0 */.a,
        _88/* s7xc */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_85/* s7wZ */, new T2(1,new T(function(){
            return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_84/* s7wY */, _87/* s7x1 */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _7Z/*  s7wX */ = _86/* s7x0 */.b;
        _80/*  s7wY */ = new T(function(){
          return E(B(_60/* FormEngine.FormItem.$wincrementNumbering */(_84/* s7wY */, _87/* s7x1 */)).a);
        });
        _81/*  s7wZ */ = _88/* s7xc */;
        return __continue/* EXTERNAL */;
      }
    })(_7Z/*  s7wX */, _80/*  s7wY */, _81/*  s7wZ */));
    if(_82/*  $wgo1 */!=__continue/* EXTERNAL */){
      return _82/*  $wgo1 */;
    }
  }
},
_89/* NoNumbering */ = __Z/* EXTERNAL */,
_8a/* remark5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Your comments"));
}),
_8b/* remark4 */ = new T1(1,_8a/* FormStructure.Common.remark5 */),
_8c/* remark3 */ = {_:0,a:_8b/* FormStructure.Common.remark4 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_8d/* remark2 */ = new T1(1,_8c/* FormStructure.Common.remark3 */),
_8e/* remark1 */ = new T2(1,_8d/* FormStructure.Common.remark2 */,_I/* GHC.Types.[] */),
_8f/* remark6 */ = 0,
_8g/* True */ = true,
_8h/* remark9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Other"));
}),
_8i/* remark8 */ = new T1(1,_8h/* FormStructure.Common.remark9 */),
_8j/* remark7 */ = {_:0,a:_8i/* FormStructure.Common.remark8 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8k/* remark */ = new T3(7,_8j/* FormStructure.Common.remark7 */,_8f/* FormStructure.Common.remark6 */,_8e/* FormStructure.Common.remark1 */),
_8l/* ch0GeneralInformation3 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_8m/* ch0GeneralInformation37 */ = 0,
_8n/* ch0GeneralInformation40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Affiliation"));
}),
_8o/* ch0GeneralInformation39 */ = new T1(1,_8n/* FormStructure.Chapter0.ch0GeneralInformation40 */),
_8p/* ch0GeneralInformation38 */ = {_:0,a:_8o/* FormStructure.Chapter0.ch0GeneralInformation39 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8q/* ch0GeneralInformation36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Country"));
}),
_8r/* ch0GeneralInformation35 */ = new T1(1,_8q/* FormStructure.Chapter0.ch0GeneralInformation36 */),
_8s/* ch0GeneralInformation34 */ = {_:0,a:_8r/* FormStructure.Chapter0.ch0GeneralInformation35 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_8t/* countries770 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("France"));
}),
_8u/* countries771 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FR"));
}),
_8v/* countries769 */ = new T2(0,_8u/* Countries.countries771 */,_8t/* Countries.countries770 */),
_8w/* countries767 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Guiana"));
}),
_8x/* countries768 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GF"));
}),
_8y/* countries766 */ = new T2(0,_8x/* Countries.countries768 */,_8w/* Countries.countries767 */),
_8z/* countries764 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Polynesia"));
}),
_8A/* countries765 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PF"));
}),
_8B/* countries763 */ = new T2(0,_8A/* Countries.countries765 */,_8z/* Countries.countries764 */),
_8C/* countries761 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Southern Territories"));
}),
_8D/* countries762 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TF"));
}),
_8E/* countries760 */ = new T2(0,_8D/* Countries.countries762 */,_8C/* Countries.countries761 */),
_8F/* countries758 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gabon"));
}),
_8G/* countries759 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GA"));
}),
_8H/* countries757 */ = new T2(0,_8G/* Countries.countries759 */,_8F/* Countries.countries758 */),
_8I/* countries755 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gambia"));
}),
_8J/* countries756 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GM"));
}),
_8K/* countries754 */ = new T2(0,_8J/* Countries.countries756 */,_8I/* Countries.countries755 */),
_8L/* countries752 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Georgia"));
}),
_8M/* countries753 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GE"));
}),
_8N/* countries751 */ = new T2(0,_8M/* Countries.countries753 */,_8L/* Countries.countries752 */),
_8O/* countries749 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Germany"));
}),
_8P/* countries750 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DE"));
}),
_8Q/* countries748 */ = new T2(0,_8P/* Countries.countries750 */,_8O/* Countries.countries749 */),
_8R/* countries746 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ghana"));
}),
_8S/* countries747 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GH"));
}),
_8T/* countries745 */ = new T2(0,_8S/* Countries.countries747 */,_8R/* Countries.countries746 */),
_8U/* countries743 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gibraltar"));
}),
_8V/* countries744 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GI"));
}),
_8W/* countries742 */ = new T2(0,_8V/* Countries.countries744 */,_8U/* Countries.countries743 */),
_8X/* countries740 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greece"));
}),
_8Y/* countries741 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GR"));
}),
_8Z/* countries739 */ = new T2(0,_8Y/* Countries.countries741 */,_8X/* Countries.countries740 */),
_90/* countries737 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greenland"));
}),
_91/* countries738 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GL"));
}),
_92/* countries736 */ = new T2(0,_91/* Countries.countries738 */,_90/* Countries.countries737 */),
_93/* countries734 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grenada"));
}),
_94/* countries735 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GD"));
}),
_95/* countries733 */ = new T2(0,_94/* Countries.countries735 */,_93/* Countries.countries734 */),
_96/* countries731 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guadeloupe"));
}),
_97/* countries732 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GP"));
}),
_98/* countries730 */ = new T2(0,_97/* Countries.countries732 */,_96/* Countries.countries731 */),
_99/* countries728 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guam"));
}),
_9a/* countries729 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GU"));
}),
_9b/* countries727 */ = new T2(0,_9a/* Countries.countries729 */,_99/* Countries.countries728 */),
_9c/* countries725 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guatemala"));
}),
_9d/* countries726 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GT"));
}),
_9e/* countries724 */ = new T2(0,_9d/* Countries.countries726 */,_9c/* Countries.countries725 */),
_9f/* countries722 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guernsey"));
}),
_9g/* countries723 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GG"));
}),
_9h/* countries721 */ = new T2(0,_9g/* Countries.countries723 */,_9f/* Countries.countries722 */),
_9i/* countries719 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea"));
}),
_9j/* countries720 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GN"));
}),
_9k/* countries718 */ = new T2(0,_9j/* Countries.countries720 */,_9i/* Countries.countries719 */),
_9l/* countries716 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea-Bissau"));
}),
_9m/* countries717 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GW"));
}),
_9n/* countries715 */ = new T2(0,_9m/* Countries.countries717 */,_9l/* Countries.countries716 */),
_9o/* countries713 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guyana"));
}),
_9p/* countries714 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GY"));
}),
_9q/* countries712 */ = new T2(0,_9p/* Countries.countries714 */,_9o/* Countries.countries713 */),
_9r/* countries710 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haiti"));
}),
_9s/* countries711 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_9t/* countries709 */ = new T2(0,_9s/* Countries.countries711 */,_9r/* Countries.countries710 */),
_9u/* countries707 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Heard Island and McDonald Islands"));
}),
_9v/* countries708 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HM"));
}),
_9w/* countries706 */ = new T2(0,_9v/* Countries.countries708 */,_9u/* Countries.countries707 */),
_9x/* countries704 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Holy See (Vatican City State)"));
}),
_9y/* countries705 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VA"));
}),
_9z/* countries703 */ = new T2(0,_9y/* Countries.countries705 */,_9x/* Countries.countries704 */),
_9A/* countries251 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zimbabwe"));
}),
_9B/* countries252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZW"));
}),
_9C/* countries250 */ = new T2(0,_9B/* Countries.countries252 */,_9A/* Countries.countries251 */),
_9D/* countries249 */ = new T2(1,_9C/* Countries.countries250 */,_I/* GHC.Types.[] */),
_9E/* countries254 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zambia"));
}),
_9F/* countries255 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZM"));
}),
_9G/* countries253 */ = new T2(0,_9F/* Countries.countries255 */,_9E/* Countries.countries254 */),
_9H/* countries248 */ = new T2(1,_9G/* Countries.countries253 */,_9D/* Countries.countries249 */),
_9I/* countries257 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yemen"));
}),
_9J/* countries258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YE"));
}),
_9K/* countries256 */ = new T2(0,_9J/* Countries.countries258 */,_9I/* Countries.countries257 */),
_9L/* countries247 */ = new T2(1,_9K/* Countries.countries256 */,_9H/* Countries.countries248 */),
_9M/* countries260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Western Sahara"));
}),
_9N/* countries261 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EH"));
}),
_9O/* countries259 */ = new T2(0,_9N/* Countries.countries261 */,_9M/* Countries.countries260 */),
_9P/* countries246 */ = new T2(1,_9O/* Countries.countries259 */,_9L/* Countries.countries247 */),
_9Q/* countries263 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Wallis and Futuna"));
}),
_9R/* countries264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WF"));
}),
_9S/* countries262 */ = new T2(0,_9R/* Countries.countries264 */,_9Q/* Countries.countries263 */),
_9T/* countries245 */ = new T2(1,_9S/* Countries.countries262 */,_9P/* Countries.countries246 */),
_9U/* countries266 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, U.S."));
}),
_9V/* countries267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VI"));
}),
_9W/* countries265 */ = new T2(0,_9V/* Countries.countries267 */,_9U/* Countries.countries266 */),
_9X/* countries244 */ = new T2(1,_9W/* Countries.countries265 */,_9T/* Countries.countries245 */),
_9Y/* countries269 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, British"));
}),
_9Z/* countries270 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VG"));
}),
_a0/* countries268 */ = new T2(0,_9Z/* Countries.countries270 */,_9Y/* Countries.countries269 */),
_a1/* countries243 */ = new T2(1,_a0/* Countries.countries268 */,_9X/* Countries.countries244 */),
_a2/* countries272 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Viet Nam"));
}),
_a3/* countries273 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VN"));
}),
_a4/* countries271 */ = new T2(0,_a3/* Countries.countries273 */,_a2/* Countries.countries272 */),
_a5/* countries242 */ = new T2(1,_a4/* Countries.countries271 */,_a1/* Countries.countries243 */),
_a6/* countries275 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Venezuela, Bolivarian Republic of"));
}),
_a7/* countries276 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VE"));
}),
_a8/* countries274 */ = new T2(0,_a7/* Countries.countries276 */,_a6/* Countries.countries275 */),
_a9/* countries241 */ = new T2(1,_a8/* Countries.countries274 */,_a5/* Countries.countries242 */),
_aa/* countries278 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Vanuatu"));
}),
_ab/* countries279 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VU"));
}),
_ac/* countries277 */ = new T2(0,_ab/* Countries.countries279 */,_aa/* Countries.countries278 */),
_ad/* countries240 */ = new T2(1,_ac/* Countries.countries277 */,_a9/* Countries.countries241 */),
_ae/* countries281 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uzbekistan"));
}),
_af/* countries282 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UZ"));
}),
_ag/* countries280 */ = new T2(0,_af/* Countries.countries282 */,_ae/* Countries.countries281 */),
_ah/* countries239 */ = new T2(1,_ag/* Countries.countries280 */,_ad/* Countries.countries240 */),
_ai/* countries284 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uruguay"));
}),
_aj/* countries285 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UY"));
}),
_ak/* countries283 */ = new T2(0,_aj/* Countries.countries285 */,_ai/* Countries.countries284 */),
_al/* countries238 */ = new T2(1,_ak/* Countries.countries283 */,_ah/* Countries.countries239 */),
_am/* countries287 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States Minor Outlying Islands"));
}),
_an/* countries288 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UM"));
}),
_ao/* countries286 */ = new T2(0,_an/* Countries.countries288 */,_am/* Countries.countries287 */),
_ap/* countries237 */ = new T2(1,_ao/* Countries.countries286 */,_al/* Countries.countries238 */),
_aq/* countries290 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States"));
}),
_ar/* countries291 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_as/* countries289 */ = new T2(0,_ar/* Countries.countries291 */,_aq/* Countries.countries290 */),
_at/* countries236 */ = new T2(1,_as/* Countries.countries289 */,_ap/* Countries.countries237 */),
_au/* countries293 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Kingdom"));
}),
_av/* countries294 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_aw/* countries292 */ = new T2(0,_av/* Countries.countries294 */,_au/* Countries.countries293 */),
_ax/* countries235 */ = new T2(1,_aw/* Countries.countries292 */,_at/* Countries.countries236 */),
_ay/* countries296 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Arab Emirates"));
}),
_az/* countries297 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AE"));
}),
_aA/* countries295 */ = new T2(0,_az/* Countries.countries297 */,_ay/* Countries.countries296 */),
_aB/* countries234 */ = new T2(1,_aA/* Countries.countries295 */,_ax/* Countries.countries235 */),
_aC/* countries299 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ukraine"));
}),
_aD/* countries300 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UA"));
}),
_aE/* countries298 */ = new T2(0,_aD/* Countries.countries300 */,_aC/* Countries.countries299 */),
_aF/* countries233 */ = new T2(1,_aE/* Countries.countries298 */,_aB/* Countries.countries234 */),
_aG/* countries302 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uganda"));
}),
_aH/* countries303 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UG"));
}),
_aI/* countries301 */ = new T2(0,_aH/* Countries.countries303 */,_aG/* Countries.countries302 */),
_aJ/* countries232 */ = new T2(1,_aI/* Countries.countries301 */,_aF/* Countries.countries233 */),
_aK/* countries305 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tuvalu"));
}),
_aL/* countries306 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TV"));
}),
_aM/* countries304 */ = new T2(0,_aL/* Countries.countries306 */,_aK/* Countries.countries305 */),
_aN/* countries231 */ = new T2(1,_aM/* Countries.countries304 */,_aJ/* Countries.countries232 */),
_aO/* countries308 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turks and Caicos Islands"));
}),
_aP/* countries309 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TC"));
}),
_aQ/* countries307 */ = new T2(0,_aP/* Countries.countries309 */,_aO/* Countries.countries308 */),
_aR/* countries230 */ = new T2(1,_aQ/* Countries.countries307 */,_aN/* Countries.countries231 */),
_aS/* countries311 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkmenistan"));
}),
_aT/* countries312 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TM"));
}),
_aU/* countries310 */ = new T2(0,_aT/* Countries.countries312 */,_aS/* Countries.countries311 */),
_aV/* countries229 */ = new T2(1,_aU/* Countries.countries310 */,_aR/* Countries.countries230 */),
_aW/* countries314 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkey"));
}),
_aX/* countries315 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TR"));
}),
_aY/* countries313 */ = new T2(0,_aX/* Countries.countries315 */,_aW/* Countries.countries314 */),
_aZ/* countries228 */ = new T2(1,_aY/* Countries.countries313 */,_aV/* Countries.countries229 */),
_b0/* countries317 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tunisia"));
}),
_b1/* countries318 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TN"));
}),
_b2/* countries316 */ = new T2(0,_b1/* Countries.countries318 */,_b0/* Countries.countries317 */),
_b3/* countries227 */ = new T2(1,_b2/* Countries.countries316 */,_aZ/* Countries.countries228 */),
_b4/* countries320 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trinidad and Tobago"));
}),
_b5/* countries321 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TT"));
}),
_b6/* countries319 */ = new T2(0,_b5/* Countries.countries321 */,_b4/* Countries.countries320 */),
_b7/* countries226 */ = new T2(1,_b6/* Countries.countries319 */,_b3/* Countries.countries227 */),
_b8/* countries323 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tonga"));
}),
_b9/* countries324 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TO"));
}),
_ba/* countries322 */ = new T2(0,_b9/* Countries.countries324 */,_b8/* Countries.countries323 */),
_bb/* countries225 */ = new T2(1,_ba/* Countries.countries322 */,_b7/* Countries.countries226 */),
_bc/* countries326 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tokelau"));
}),
_bd/* countries327 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TK"));
}),
_be/* countries325 */ = new T2(0,_bd/* Countries.countries327 */,_bc/* Countries.countries326 */),
_bf/* countries224 */ = new T2(1,_be/* Countries.countries325 */,_bb/* Countries.countries225 */),
_bg/* countries329 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Togo"));
}),
_bh/* countries330 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TG"));
}),
_bi/* countries328 */ = new T2(0,_bh/* Countries.countries330 */,_bg/* Countries.countries329 */),
_bj/* countries223 */ = new T2(1,_bi/* Countries.countries328 */,_bf/* Countries.countries224 */),
_bk/* countries332 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Timor-Leste"));
}),
_bl/* countries333 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TL"));
}),
_bm/* countries331 */ = new T2(0,_bl/* Countries.countries333 */,_bk/* Countries.countries332 */),
_bn/* countries222 */ = new T2(1,_bm/* Countries.countries331 */,_bj/* Countries.countries223 */),
_bo/* countries335 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Thailand"));
}),
_bp/* countries336 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TH"));
}),
_bq/* countries334 */ = new T2(0,_bp/* Countries.countries336 */,_bo/* Countries.countries335 */),
_br/* countries221 */ = new T2(1,_bq/* Countries.countries334 */,_bn/* Countries.countries222 */),
_bs/* countries338 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tanzania, United Republic of"));
}),
_bt/* countries339 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TZ"));
}),
_bu/* countries337 */ = new T2(0,_bt/* Countries.countries339 */,_bs/* Countries.countries338 */),
_bv/* countries220 */ = new T2(1,_bu/* Countries.countries337 */,_br/* Countries.countries221 */),
_bw/* countries341 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tajikistan"));
}),
_bx/* countries342 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TJ"));
}),
_by/* countries340 */ = new T2(0,_bx/* Countries.countries342 */,_bw/* Countries.countries341 */),
_bz/* countries219 */ = new T2(1,_by/* Countries.countries340 */,_bv/* Countries.countries220 */),
_bA/* countries344 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Taiwan, Province of China"));
}),
_bB/* countries345 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TW"));
}),
_bC/* countries343 */ = new T2(0,_bB/* Countries.countries345 */,_bA/* Countries.countries344 */),
_bD/* countries218 */ = new T2(1,_bC/* Countries.countries343 */,_bz/* Countries.countries219 */),
_bE/* countries347 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Syrian Arab Republic"));
}),
_bF/* countries348 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SY"));
}),
_bG/* countries346 */ = new T2(0,_bF/* Countries.countries348 */,_bE/* Countries.countries347 */),
_bH/* countries217 */ = new T2(1,_bG/* Countries.countries346 */,_bD/* Countries.countries218 */),
_bI/* countries350 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Switzerland"));
}),
_bJ/* countries351 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CH"));
}),
_bK/* countries349 */ = new T2(0,_bJ/* Countries.countries351 */,_bI/* Countries.countries350 */),
_bL/* countries216 */ = new T2(1,_bK/* Countries.countries349 */,_bH/* Countries.countries217 */),
_bM/* countries353 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sweden"));
}),
_bN/* countries354 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SE"));
}),
_bO/* countries352 */ = new T2(0,_bN/* Countries.countries354 */,_bM/* Countries.countries353 */),
_bP/* countries215 */ = new T2(1,_bO/* Countries.countries352 */,_bL/* Countries.countries216 */),
_bQ/* countries356 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Swaziland"));
}),
_bR/* countries357 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SZ"));
}),
_bS/* countries355 */ = new T2(0,_bR/* Countries.countries357 */,_bQ/* Countries.countries356 */),
_bT/* countries214 */ = new T2(1,_bS/* Countries.countries355 */,_bP/* Countries.countries215 */),
_bU/* countries359 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Svalbard and Jan Mayen"));
}),
_bV/* countries360 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SJ"));
}),
_bW/* countries358 */ = new T2(0,_bV/* Countries.countries360 */,_bU/* Countries.countries359 */),
_bX/* countries213 */ = new T2(1,_bW/* Countries.countries358 */,_bT/* Countries.countries214 */),
_bY/* countries362 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Suriname"));
}),
_bZ/* countries363 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SR"));
}),
_c0/* countries361 */ = new T2(0,_bZ/* Countries.countries363 */,_bY/* Countries.countries362 */),
_c1/* countries212 */ = new T2(1,_c0/* Countries.countries361 */,_bX/* Countries.countries213 */),
_c2/* countries365 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sudan"));
}),
_c3/* countries366 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SD"));
}),
_c4/* countries364 */ = new T2(0,_c3/* Countries.countries366 */,_c2/* Countries.countries365 */),
_c5/* countries211 */ = new T2(1,_c4/* Countries.countries364 */,_c1/* Countries.countries212 */),
_c6/* countries368 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sri Lanka"));
}),
_c7/* countries369 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LK"));
}),
_c8/* countries367 */ = new T2(0,_c7/* Countries.countries369 */,_c6/* Countries.countries368 */),
_c9/* countries210 */ = new T2(1,_c8/* Countries.countries367 */,_c5/* Countries.countries211 */),
_ca/* countries371 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Spain"));
}),
_cb/* countries372 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ES"));
}),
_cc/* countries370 */ = new T2(0,_cb/* Countries.countries372 */,_ca/* Countries.countries371 */),
_cd/* countries209 */ = new T2(1,_cc/* Countries.countries370 */,_c9/* Countries.countries210 */),
_ce/* countries374 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Sudan"));
}),
_cf/* countries375 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SS"));
}),
_cg/* countries373 */ = new T2(0,_cf/* Countries.countries375 */,_ce/* Countries.countries374 */),
_ch/* countries208 */ = new T2(1,_cg/* Countries.countries373 */,_cd/* Countries.countries209 */),
_ci/* countries377 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Georgia and the South Sandwich Islands"));
}),
_cj/* countries378 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_ck/* countries376 */ = new T2(0,_cj/* Countries.countries378 */,_ci/* Countries.countries377 */),
_cl/* countries207 */ = new T2(1,_ck/* Countries.countries376 */,_ch/* Countries.countries208 */),
_cm/* countries380 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Africa"));
}),
_cn/* countries381 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZA"));
}),
_co/* countries379 */ = new T2(0,_cn/* Countries.countries381 */,_cm/* Countries.countries380 */),
_cp/* countries206 */ = new T2(1,_co/* Countries.countries379 */,_cl/* Countries.countries207 */),
_cq/* countries383 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Somalia"));
}),
_cr/* countries384 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_cs/* countries382 */ = new T2(0,_cr/* Countries.countries384 */,_cq/* Countries.countries383 */),
_ct/* countries205 */ = new T2(1,_cs/* Countries.countries382 */,_cp/* Countries.countries206 */),
_cu/* countries386 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Solomon Islands"));
}),
_cv/* countries387 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SB"));
}),
_cw/* countries385 */ = new T2(0,_cv/* Countries.countries387 */,_cu/* Countries.countries386 */),
_cx/* countries204 */ = new T2(1,_cw/* Countries.countries385 */,_ct/* Countries.countries205 */),
_cy/* countries389 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovenia"));
}),
_cz/* countries390 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_cA/* countries388 */ = new T2(0,_cz/* Countries.countries390 */,_cy/* Countries.countries389 */),
_cB/* countries203 */ = new T2(1,_cA/* Countries.countries388 */,_cx/* Countries.countries204 */),
_cC/* countries392 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovakia"));
}),
_cD/* countries393 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SK"));
}),
_cE/* countries391 */ = new T2(0,_cD/* Countries.countries393 */,_cC/* Countries.countries392 */),
_cF/* countries202 */ = new T2(1,_cE/* Countries.countries391 */,_cB/* Countries.countries203 */),
_cG/* countries395 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sint Maarten (Dutch part)"));
}),
_cH/* countries396 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SX"));
}),
_cI/* countries394 */ = new T2(0,_cH/* Countries.countries396 */,_cG/* Countries.countries395 */),
_cJ/* countries201 */ = new T2(1,_cI/* Countries.countries394 */,_cF/* Countries.countries202 */),
_cK/* countries398 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Singapore"));
}),
_cL/* countries399 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SG"));
}),
_cM/* countries397 */ = new T2(0,_cL/* Countries.countries399 */,_cK/* Countries.countries398 */),
_cN/* countries200 */ = new T2(1,_cM/* Countries.countries397 */,_cJ/* Countries.countries201 */),
_cO/* countries401 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sierra Leone"));
}),
_cP/* countries402 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SL"));
}),
_cQ/* countries400 */ = new T2(0,_cP/* Countries.countries402 */,_cO/* Countries.countries401 */),
_cR/* countries199 */ = new T2(1,_cQ/* Countries.countries400 */,_cN/* Countries.countries200 */),
_cS/* countries404 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Seychelles"));
}),
_cT/* countries405 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SC"));
}),
_cU/* countries403 */ = new T2(0,_cT/* Countries.countries405 */,_cS/* Countries.countries404 */),
_cV/* countries198 */ = new T2(1,_cU/* Countries.countries403 */,_cR/* Countries.countries199 */),
_cW/* countries407 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Serbia"));
}),
_cX/* countries408 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_cY/* countries406 */ = new T2(0,_cX/* Countries.countries408 */,_cW/* Countries.countries407 */),
_cZ/* countries197 */ = new T2(1,_cY/* Countries.countries406 */,_cV/* Countries.countries198 */),
_d0/* countries410 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Senegal"));
}),
_d1/* countries411 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SN"));
}),
_d2/* countries409 */ = new T2(0,_d1/* Countries.countries411 */,_d0/* Countries.countries410 */),
_d3/* countries196 */ = new T2(1,_d2/* Countries.countries409 */,_cZ/* Countries.countries197 */),
_d4/* countries413 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saudi Arabia"));
}),
_d5/* countries414 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SA"));
}),
_d6/* countries412 */ = new T2(0,_d5/* Countries.countries414 */,_d4/* Countries.countries413 */),
_d7/* countries195 */ = new T2(1,_d6/* Countries.countries412 */,_d3/* Countries.countries196 */),
_d8/* countries416 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sao Tome and Principe"));
}),
_d9/* countries417 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ST"));
}),
_da/* countries415 */ = new T2(0,_d9/* Countries.countries417 */,_d8/* Countries.countries416 */),
_db/* countries194 */ = new T2(1,_da/* Countries.countries415 */,_d7/* Countries.countries195 */),
_dc/* countries419 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("San Marino"));
}),
_dd/* countries420 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SM"));
}),
_de/* countries418 */ = new T2(0,_dd/* Countries.countries420 */,_dc/* Countries.countries419 */),
_df/* countries193 */ = new T2(1,_de/* Countries.countries418 */,_db/* Countries.countries194 */),
_dg/* countries422 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Samoa"));
}),
_dh/* countries423 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WS"));
}),
_di/* countries421 */ = new T2(0,_dh/* Countries.countries423 */,_dg/* Countries.countries422 */),
_dj/* countries192 */ = new T2(1,_di/* Countries.countries421 */,_df/* Countries.countries193 */),
_dk/* countries425 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Vincent and the Grenadines"));
}),
_dl/* countries426 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VC"));
}),
_dm/* countries424 */ = new T2(0,_dl/* Countries.countries426 */,_dk/* Countries.countries425 */),
_dn/* countries191 */ = new T2(1,_dm/* Countries.countries424 */,_dj/* Countries.countries192 */),
_do/* countries428 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Pierre and Miquelon"));
}),
_dp/* countries429 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PM"));
}),
_dq/* countries427 */ = new T2(0,_dp/* Countries.countries429 */,_do/* Countries.countries428 */),
_dr/* countries190 */ = new T2(1,_dq/* Countries.countries427 */,_dn/* Countries.countries191 */),
_ds/* countries431 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Martin (French part)"));
}),
_dt/* countries432 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MF"));
}),
_du/* countries430 */ = new T2(0,_dt/* Countries.countries432 */,_ds/* Countries.countries431 */),
_dv/* countries189 */ = new T2(1,_du/* Countries.countries430 */,_dr/* Countries.countries190 */),
_dw/* countries434 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Lucia"));
}),
_dx/* countries435 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LC"));
}),
_dy/* countries433 */ = new T2(0,_dx/* Countries.countries435 */,_dw/* Countries.countries434 */),
_dz/* countries188 */ = new T2(1,_dy/* Countries.countries433 */,_dv/* Countries.countries189 */),
_dA/* countries437 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Kitts and Nevis"));
}),
_dB/* countries438 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KN"));
}),
_dC/* countries436 */ = new T2(0,_dB/* Countries.countries438 */,_dA/* Countries.countries437 */),
_dD/* countries187 */ = new T2(1,_dC/* Countries.countries436 */,_dz/* Countries.countries188 */),
_dE/* countries440 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Helena, Ascension and Tristan da Cunha"));
}),
_dF/* countries441 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SH"));
}),
_dG/* countries439 */ = new T2(0,_dF/* Countries.countries441 */,_dE/* Countries.countries440 */),
_dH/* countries186 */ = new T2(1,_dG/* Countries.countries439 */,_dD/* Countries.countries187 */),
_dI/* countries443 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Barth\u00e9lemy"));
}),
_dJ/* countries444 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BL"));
}),
_dK/* countries442 */ = new T2(0,_dJ/* Countries.countries444 */,_dI/* Countries.countries443 */),
_dL/* countries185 */ = new T2(1,_dK/* Countries.countries442 */,_dH/* Countries.countries186 */),
_dM/* countries446 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rwanda"));
}),
_dN/* countries447 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RW"));
}),
_dO/* countries445 */ = new T2(0,_dN/* Countries.countries447 */,_dM/* Countries.countries446 */),
_dP/* countries184 */ = new T2(1,_dO/* Countries.countries445 */,_dL/* Countries.countries185 */),
_dQ/* countries449 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Russian Federation"));
}),
_dR/* countries450 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RU"));
}),
_dS/* countries448 */ = new T2(0,_dR/* Countries.countries450 */,_dQ/* Countries.countries449 */),
_dT/* countries183 */ = new T2(1,_dS/* Countries.countries448 */,_dP/* Countries.countries184 */),
_dU/* countries452 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Romania"));
}),
_dV/* countries453 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RO"));
}),
_dW/* countries451 */ = new T2(0,_dV/* Countries.countries453 */,_dU/* Countries.countries452 */),
_dX/* countries182 */ = new T2(1,_dW/* Countries.countries451 */,_dT/* Countries.countries183 */),
_dY/* countries455 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("R\u00e9union"));
}),
_dZ/* countries456 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RE"));
}),
_e0/* countries454 */ = new T2(0,_dZ/* Countries.countries456 */,_dY/* Countries.countries455 */),
_e1/* countries181 */ = new T2(1,_e0/* Countries.countries454 */,_dX/* Countries.countries182 */),
_e2/* countries458 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Qatar"));
}),
_e3/* countries459 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("QA"));
}),
_e4/* countries457 */ = new T2(0,_e3/* Countries.countries459 */,_e2/* Countries.countries458 */),
_e5/* countries180 */ = new T2(1,_e4/* Countries.countries457 */,_e1/* Countries.countries181 */),
_e6/* countries461 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Puerto Rico"));
}),
_e7/* countries462 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PR"));
}),
_e8/* countries460 */ = new T2(0,_e7/* Countries.countries462 */,_e6/* Countries.countries461 */),
_e9/* countries179 */ = new T2(1,_e8/* Countries.countries460 */,_e5/* Countries.countries180 */),
_ea/* countries464 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Portugal"));
}),
_eb/* countries465 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PT"));
}),
_ec/* countries463 */ = new T2(0,_eb/* Countries.countries465 */,_ea/* Countries.countries464 */),
_ed/* countries178 */ = new T2(1,_ec/* Countries.countries463 */,_e9/* Countries.countries179 */),
_ee/* countries467 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Poland"));
}),
_ef/* countries468 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PL"));
}),
_eg/* countries466 */ = new T2(0,_ef/* Countries.countries468 */,_ee/* Countries.countries467 */),
_eh/* countries177 */ = new T2(1,_eg/* Countries.countries466 */,_ed/* Countries.countries178 */),
_ei/* countries470 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pitcairn"));
}),
_ej/* countries471 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PN"));
}),
_ek/* countries469 */ = new T2(0,_ej/* Countries.countries471 */,_ei/* Countries.countries470 */),
_el/* countries176 */ = new T2(1,_ek/* Countries.countries469 */,_eh/* Countries.countries177 */),
_em/* countries473 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Philippines"));
}),
_en/* countries474 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PH"));
}),
_eo/* countries472 */ = new T2(0,_en/* Countries.countries474 */,_em/* Countries.countries473 */),
_ep/* countries175 */ = new T2(1,_eo/* Countries.countries472 */,_el/* Countries.countries176 */),
_eq/* countries476 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Peru"));
}),
_er/* countries477 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PE"));
}),
_es/* countries475 */ = new T2(0,_er/* Countries.countries477 */,_eq/* Countries.countries476 */),
_et/* countries174 */ = new T2(1,_es/* Countries.countries475 */,_ep/* Countries.countries175 */),
_eu/* countries479 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Paraguay"));
}),
_ev/* countries480 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PY"));
}),
_ew/* countries478 */ = new T2(0,_ev/* Countries.countries480 */,_eu/* Countries.countries479 */),
_ex/* countries173 */ = new T2(1,_ew/* Countries.countries478 */,_et/* Countries.countries174 */),
_ey/* countries482 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Papua New Guinea"));
}),
_ez/* countries483 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PG"));
}),
_eA/* countries481 */ = new T2(0,_ez/* Countries.countries483 */,_ey/* Countries.countries482 */),
_eB/* countries172 */ = new T2(1,_eA/* Countries.countries481 */,_ex/* Countries.countries173 */),
_eC/* countries485 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Panama"));
}),
_eD/* countries486 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PA"));
}),
_eE/* countries484 */ = new T2(0,_eD/* Countries.countries486 */,_eC/* Countries.countries485 */),
_eF/* countries171 */ = new T2(1,_eE/* Countries.countries484 */,_eB/* Countries.countries172 */),
_eG/* countries488 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palestinian Territory, Occupied"));
}),
_eH/* countries489 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PS"));
}),
_eI/* countries487 */ = new T2(0,_eH/* Countries.countries489 */,_eG/* Countries.countries488 */),
_eJ/* countries170 */ = new T2(1,_eI/* Countries.countries487 */,_eF/* Countries.countries171 */),
_eK/* countries491 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palau"));
}),
_eL/* countries492 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PW"));
}),
_eM/* countries490 */ = new T2(0,_eL/* Countries.countries492 */,_eK/* Countries.countries491 */),
_eN/* countries169 */ = new T2(1,_eM/* Countries.countries490 */,_eJ/* Countries.countries170 */),
_eO/* countries494 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pakistan"));
}),
_eP/* countries495 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PK"));
}),
_eQ/* countries493 */ = new T2(0,_eP/* Countries.countries495 */,_eO/* Countries.countries494 */),
_eR/* countries168 */ = new T2(1,_eQ/* Countries.countries493 */,_eN/* Countries.countries169 */),
_eS/* countries497 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Oman"));
}),
_eT/* countries498 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OM"));
}),
_eU/* countries496 */ = new T2(0,_eT/* Countries.countries498 */,_eS/* Countries.countries497 */),
_eV/* countries167 */ = new T2(1,_eU/* Countries.countries496 */,_eR/* Countries.countries168 */),
_eW/* countries500 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norway"));
}),
_eX/* countries501 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NO"));
}),
_eY/* countries499 */ = new T2(0,_eX/* Countries.countries501 */,_eW/* Countries.countries500 */),
_eZ/* countries166 */ = new T2(1,_eY/* Countries.countries499 */,_eV/* Countries.countries167 */),
_f0/* countries503 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Northern Mariana Islands"));
}),
_f1/* countries504 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MP"));
}),
_f2/* countries502 */ = new T2(0,_f1/* Countries.countries504 */,_f0/* Countries.countries503 */),
_f3/* countries165 */ = new T2(1,_f2/* Countries.countries502 */,_eZ/* Countries.countries166 */),
_f4/* countries506 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norfolk Island"));
}),
_f5/* countries507 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NF"));
}),
_f6/* countries505 */ = new T2(0,_f5/* Countries.countries507 */,_f4/* Countries.countries506 */),
_f7/* countries164 */ = new T2(1,_f6/* Countries.countries505 */,_f3/* Countries.countries165 */),
_f8/* countries509 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niue"));
}),
_f9/* countries510 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NU"));
}),
_fa/* countries508 */ = new T2(0,_f9/* Countries.countries510 */,_f8/* Countries.countries509 */),
_fb/* countries163 */ = new T2(1,_fa/* Countries.countries508 */,_f7/* Countries.countries164 */),
_fc/* countries512 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nigeria"));
}),
_fd/* countries513 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NG"));
}),
_fe/* countries511 */ = new T2(0,_fd/* Countries.countries513 */,_fc/* Countries.countries512 */),
_ff/* countries162 */ = new T2(1,_fe/* Countries.countries511 */,_fb/* Countries.countries163 */),
_fg/* countries515 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niger"));
}),
_fh/* countries516 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NE"));
}),
_fi/* countries514 */ = new T2(0,_fh/* Countries.countries516 */,_fg/* Countries.countries515 */),
_fj/* countries161 */ = new T2(1,_fi/* Countries.countries514 */,_ff/* Countries.countries162 */),
_fk/* countries518 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nicaragua"));
}),
_fl/* countries519 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NI"));
}),
_fm/* countries517 */ = new T2(0,_fl/* Countries.countries519 */,_fk/* Countries.countries518 */),
_fn/* countries160 */ = new T2(1,_fm/* Countries.countries517 */,_fj/* Countries.countries161 */),
_fo/* countries521 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Zealand"));
}),
_fp/* countries522 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NZ"));
}),
_fq/* countries520 */ = new T2(0,_fp/* Countries.countries522 */,_fo/* Countries.countries521 */),
_fr/* countries159 */ = new T2(1,_fq/* Countries.countries520 */,_fn/* Countries.countries160 */),
_fs/* countries524 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Caledonia"));
}),
_ft/* countries525 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NC"));
}),
_fu/* countries523 */ = new T2(0,_ft/* Countries.countries525 */,_fs/* Countries.countries524 */),
_fv/* countries158 */ = new T2(1,_fu/* Countries.countries523 */,_fr/* Countries.countries159 */),
_fw/* countries527 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Netherlands"));
}),
_fx/* countries528 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NL"));
}),
_fy/* countries526 */ = new T2(0,_fx/* Countries.countries528 */,_fw/* Countries.countries527 */),
_fz/* countries157 */ = new T2(1,_fy/* Countries.countries526 */,_fv/* Countries.countries158 */),
_fA/* countries530 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nepal"));
}),
_fB/* countries531 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NP"));
}),
_fC/* countries529 */ = new T2(0,_fB/* Countries.countries531 */,_fA/* Countries.countries530 */),
_fD/* countries156 */ = new T2(1,_fC/* Countries.countries529 */,_fz/* Countries.countries157 */),
_fE/* countries533 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nauru"));
}),
_fF/* countries534 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NR"));
}),
_fG/* countries532 */ = new T2(0,_fF/* Countries.countries534 */,_fE/* Countries.countries533 */),
_fH/* countries155 */ = new T2(1,_fG/* Countries.countries532 */,_fD/* Countries.countries156 */),
_fI/* countries536 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Namibia"));
}),
_fJ/* countries537 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NA"));
}),
_fK/* countries535 */ = new T2(0,_fJ/* Countries.countries537 */,_fI/* Countries.countries536 */),
_fL/* countries154 */ = new T2(1,_fK/* Countries.countries535 */,_fH/* Countries.countries155 */),
_fM/* countries539 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Myanmar"));
}),
_fN/* countries540 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MM"));
}),
_fO/* countries538 */ = new T2(0,_fN/* Countries.countries540 */,_fM/* Countries.countries539 */),
_fP/* countries153 */ = new T2(1,_fO/* Countries.countries538 */,_fL/* Countries.countries154 */),
_fQ/* countries542 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mozambique"));
}),
_fR/* countries543 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MZ"));
}),
_fS/* countries541 */ = new T2(0,_fR/* Countries.countries543 */,_fQ/* Countries.countries542 */),
_fT/* countries152 */ = new T2(1,_fS/* Countries.countries541 */,_fP/* Countries.countries153 */),
_fU/* countries545 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Morocco"));
}),
_fV/* countries546 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MA"));
}),
_fW/* countries544 */ = new T2(0,_fV/* Countries.countries546 */,_fU/* Countries.countries545 */),
_fX/* countries151 */ = new T2(1,_fW/* Countries.countries544 */,_fT/* Countries.countries152 */),
_fY/* countries548 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montserrat"));
}),
_fZ/* countries549 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MS"));
}),
_g0/* countries547 */ = new T2(0,_fZ/* Countries.countries549 */,_fY/* Countries.countries548 */),
_g1/* countries150 */ = new T2(1,_g0/* Countries.countries547 */,_fX/* Countries.countries151 */),
_g2/* countries551 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montenegro"));
}),
_g3/* countries552 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ME"));
}),
_g4/* countries550 */ = new T2(0,_g3/* Countries.countries552 */,_g2/* Countries.countries551 */),
_g5/* countries149 */ = new T2(1,_g4/* Countries.countries550 */,_g1/* Countries.countries150 */),
_g6/* countries554 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mongolia"));
}),
_g7/* countries555 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MN"));
}),
_g8/* countries553 */ = new T2(0,_g7/* Countries.countries555 */,_g6/* Countries.countries554 */),
_g9/* countries148 */ = new T2(1,_g8/* Countries.countries553 */,_g5/* Countries.countries149 */),
_ga/* countries557 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Monaco"));
}),
_gb/* countries558 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MC"));
}),
_gc/* countries556 */ = new T2(0,_gb/* Countries.countries558 */,_ga/* Countries.countries557 */),
_gd/* countries147 */ = new T2(1,_gc/* Countries.countries556 */,_g9/* Countries.countries148 */),
_ge/* countries560 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Moldova, Republic of"));
}),
_gf/* countries561 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MD"));
}),
_gg/* countries559 */ = new T2(0,_gf/* Countries.countries561 */,_ge/* Countries.countries560 */),
_gh/* countries146 */ = new T2(1,_gg/* Countries.countries559 */,_gd/* Countries.countries147 */),
_gi/* countries563 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Micronesia, Federated States of"));
}),
_gj/* countries564 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FM"));
}),
_gk/* countries562 */ = new T2(0,_gj/* Countries.countries564 */,_gi/* Countries.countries563 */),
_gl/* countries145 */ = new T2(1,_gk/* Countries.countries562 */,_gh/* Countries.countries146 */),
_gm/* countries566 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mexico"));
}),
_gn/* countries567 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MX"));
}),
_go/* countries565 */ = new T2(0,_gn/* Countries.countries567 */,_gm/* Countries.countries566 */),
_gp/* countries144 */ = new T2(1,_go/* Countries.countries565 */,_gl/* Countries.countries145 */),
_gq/* countries569 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mayotte"));
}),
_gr/* countries570 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YT"));
}),
_gs/* countries568 */ = new T2(0,_gr/* Countries.countries570 */,_gq/* Countries.countries569 */),
_gt/* countries143 */ = new T2(1,_gs/* Countries.countries568 */,_gp/* Countries.countries144 */),
_gu/* countries572 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritius"));
}),
_gv/* countries573 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MU"));
}),
_gw/* countries571 */ = new T2(0,_gv/* Countries.countries573 */,_gu/* Countries.countries572 */),
_gx/* countries142 */ = new T2(1,_gw/* Countries.countries571 */,_gt/* Countries.countries143 */),
_gy/* countries575 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritania"));
}),
_gz/* countries576 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MR"));
}),
_gA/* countries574 */ = new T2(0,_gz/* Countries.countries576 */,_gy/* Countries.countries575 */),
_gB/* countries141 */ = new T2(1,_gA/* Countries.countries574 */,_gx/* Countries.countries142 */),
_gC/* countries578 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Martinique"));
}),
_gD/* countries579 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MQ"));
}),
_gE/* countries577 */ = new T2(0,_gD/* Countries.countries579 */,_gC/* Countries.countries578 */),
_gF/* countries140 */ = new T2(1,_gE/* Countries.countries577 */,_gB/* Countries.countries141 */),
_gG/* countries581 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Marshall Islands"));
}),
_gH/* countries582 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MH"));
}),
_gI/* countries580 */ = new T2(0,_gH/* Countries.countries582 */,_gG/* Countries.countries581 */),
_gJ/* countries139 */ = new T2(1,_gI/* Countries.countries580 */,_gF/* Countries.countries140 */),
_gK/* countries584 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malta"));
}),
_gL/* countries585 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MT"));
}),
_gM/* countries583 */ = new T2(0,_gL/* Countries.countries585 */,_gK/* Countries.countries584 */),
_gN/* countries138 */ = new T2(1,_gM/* Countries.countries583 */,_gJ/* Countries.countries139 */),
_gO/* countries587 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mali"));
}),
_gP/* countries588 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ML"));
}),
_gQ/* countries586 */ = new T2(0,_gP/* Countries.countries588 */,_gO/* Countries.countries587 */),
_gR/* countries137 */ = new T2(1,_gQ/* Countries.countries586 */,_gN/* Countries.countries138 */),
_gS/* countries590 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maldives"));
}),
_gT/* countries591 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MV"));
}),
_gU/* countries589 */ = new T2(0,_gT/* Countries.countries591 */,_gS/* Countries.countries590 */),
_gV/* countries136 */ = new T2(1,_gU/* Countries.countries589 */,_gR/* Countries.countries137 */),
_gW/* countries593 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malaysia"));
}),
_gX/* countries594 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MY"));
}),
_gY/* countries592 */ = new T2(0,_gX/* Countries.countries594 */,_gW/* Countries.countries593 */),
_gZ/* countries135 */ = new T2(1,_gY/* Countries.countries592 */,_gV/* Countries.countries136 */),
_h0/* countries596 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malawi"));
}),
_h1/* countries597 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MW"));
}),
_h2/* countries595 */ = new T2(0,_h1/* Countries.countries597 */,_h0/* Countries.countries596 */),
_h3/* countries134 */ = new T2(1,_h2/* Countries.countries595 */,_gZ/* Countries.countries135 */),
_h4/* countries599 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Madagascar"));
}),
_h5/* countries600 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MG"));
}),
_h6/* countries598 */ = new T2(0,_h5/* Countries.countries600 */,_h4/* Countries.countries599 */),
_h7/* countries133 */ = new T2(1,_h6/* Countries.countries598 */,_h3/* Countries.countries134 */),
_h8/* countries602 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macedonia, the former Yugoslav Republic of"));
}),
_h9/* countries603 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MK"));
}),
_ha/* countries601 */ = new T2(0,_h9/* Countries.countries603 */,_h8/* Countries.countries602 */),
_hb/* countries132 */ = new T2(1,_ha/* Countries.countries601 */,_h7/* Countries.countries133 */),
_hc/* countries605 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macao"));
}),
_hd/* countries606 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MO"));
}),
_he/* countries604 */ = new T2(0,_hd/* Countries.countries606 */,_hc/* Countries.countries605 */),
_hf/* countries131 */ = new T2(1,_he/* Countries.countries604 */,_hb/* Countries.countries132 */),
_hg/* countries608 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Luxembourg"));
}),
_hh/* countries609 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LU"));
}),
_hi/* countries607 */ = new T2(0,_hh/* Countries.countries609 */,_hg/* Countries.countries608 */),
_hj/* countries130 */ = new T2(1,_hi/* Countries.countries607 */,_hf/* Countries.countries131 */),
_hk/* countries611 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lithuania"));
}),
_hl/* countries612 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LT"));
}),
_hm/* countries610 */ = new T2(0,_hl/* Countries.countries612 */,_hk/* Countries.countries611 */),
_hn/* countries129 */ = new T2(1,_hm/* Countries.countries610 */,_hj/* Countries.countries130 */),
_ho/* countries614 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liechtenstein"));
}),
_hp/* countries615 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LI"));
}),
_hq/* countries613 */ = new T2(0,_hp/* Countries.countries615 */,_ho/* Countries.countries614 */),
_hr/* countries128 */ = new T2(1,_hq/* Countries.countries613 */,_hn/* Countries.countries129 */),
_hs/* countries617 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Libya"));
}),
_ht/* countries618 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LY"));
}),
_hu/* countries616 */ = new T2(0,_ht/* Countries.countries618 */,_hs/* Countries.countries617 */),
_hv/* countries127 */ = new T2(1,_hu/* Countries.countries616 */,_hr/* Countries.countries128 */),
_hw/* countries620 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liberia"));
}),
_hx/* countries621 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LR"));
}),
_hy/* countries619 */ = new T2(0,_hx/* Countries.countries621 */,_hw/* Countries.countries620 */),
_hz/* countries126 */ = new T2(1,_hy/* Countries.countries619 */,_hv/* Countries.countries127 */),
_hA/* countries623 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lesotho"));
}),
_hB/* countries624 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LS"));
}),
_hC/* countries622 */ = new T2(0,_hB/* Countries.countries624 */,_hA/* Countries.countries623 */),
_hD/* countries125 */ = new T2(1,_hC/* Countries.countries622 */,_hz/* Countries.countries126 */),
_hE/* countries626 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lebanon"));
}),
_hF/* countries627 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LB"));
}),
_hG/* countries625 */ = new T2(0,_hF/* Countries.countries627 */,_hE/* Countries.countries626 */),
_hH/* countries124 */ = new T2(1,_hG/* Countries.countries625 */,_hD/* Countries.countries125 */),
_hI/* countries629 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Latvia"));
}),
_hJ/* countries630 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LV"));
}),
_hK/* countries628 */ = new T2(0,_hJ/* Countries.countries630 */,_hI/* Countries.countries629 */),
_hL/* countries123 */ = new T2(1,_hK/* Countries.countries628 */,_hH/* Countries.countries124 */),
_hM/* countries632 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lao People\'s Democratic Republic"));
}),
_hN/* countries633 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LA"));
}),
_hO/* countries631 */ = new T2(0,_hN/* Countries.countries633 */,_hM/* Countries.countries632 */),
_hP/* countries122 */ = new T2(1,_hO/* Countries.countries631 */,_hL/* Countries.countries123 */),
_hQ/* countries635 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kyrgyzstan"));
}),
_hR/* countries636 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KG"));
}),
_hS/* countries634 */ = new T2(0,_hR/* Countries.countries636 */,_hQ/* Countries.countries635 */),
_hT/* countries121 */ = new T2(1,_hS/* Countries.countries634 */,_hP/* Countries.countries122 */),
_hU/* countries638 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kuwait"));
}),
_hV/* countries639 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KW"));
}),
_hW/* countries637 */ = new T2(0,_hV/* Countries.countries639 */,_hU/* Countries.countries638 */),
_hX/* countries120 */ = new T2(1,_hW/* Countries.countries637 */,_hT/* Countries.countries121 */),
_hY/* countries641 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Republic of"));
}),
_hZ/* countries642 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KR"));
}),
_i0/* countries640 */ = new T2(0,_hZ/* Countries.countries642 */,_hY/* Countries.countries641 */),
_i1/* countries119 */ = new T2(1,_i0/* Countries.countries640 */,_hX/* Countries.countries120 */),
_i2/* countries644 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Democratic People\'s Republic of"));
}),
_i3/* countries645 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KP"));
}),
_i4/* countries643 */ = new T2(0,_i3/* Countries.countries645 */,_i2/* Countries.countries644 */),
_i5/* countries118 */ = new T2(1,_i4/* Countries.countries643 */,_i1/* Countries.countries119 */),
_i6/* countries647 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kiribati"));
}),
_i7/* countries648 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KI"));
}),
_i8/* countries646 */ = new T2(0,_i7/* Countries.countries648 */,_i6/* Countries.countries647 */),
_i9/* countries117 */ = new T2(1,_i8/* Countries.countries646 */,_i5/* Countries.countries118 */),
_ia/* countries650 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kenya"));
}),
_ib/* countries651 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KE"));
}),
_ic/* countries649 */ = new T2(0,_ib/* Countries.countries651 */,_ia/* Countries.countries650 */),
_id/* countries116 */ = new T2(1,_ic/* Countries.countries649 */,_i9/* Countries.countries117 */),
_ie/* countries653 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kazakhstan"));
}),
_if/* countries654 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KZ"));
}),
_ig/* countries652 */ = new T2(0,_if/* Countries.countries654 */,_ie/* Countries.countries653 */),
_ih/* countries115 */ = new T2(1,_ig/* Countries.countries652 */,_id/* Countries.countries116 */),
_ii/* countries656 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jordan"));
}),
_ij/* countries657 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JO"));
}),
_ik/* countries655 */ = new T2(0,_ij/* Countries.countries657 */,_ii/* Countries.countries656 */),
_il/* countries114 */ = new T2(1,_ik/* Countries.countries655 */,_ih/* Countries.countries115 */),
_im/* countries659 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jersey"));
}),
_in/* countries660 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JE"));
}),
_io/* countries658 */ = new T2(0,_in/* Countries.countries660 */,_im/* Countries.countries659 */),
_ip/* countries113 */ = new T2(1,_io/* Countries.countries658 */,_il/* Countries.countries114 */),
_iq/* countries662 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Japan"));
}),
_ir/* countries663 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JP"));
}),
_is/* countries661 */ = new T2(0,_ir/* Countries.countries663 */,_iq/* Countries.countries662 */),
_it/* countries112 */ = new T2(1,_is/* Countries.countries661 */,_ip/* Countries.countries113 */),
_iu/* countries665 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jamaica"));
}),
_iv/* countries666 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JM"));
}),
_iw/* countries664 */ = new T2(0,_iv/* Countries.countries666 */,_iu/* Countries.countries665 */),
_ix/* countries111 */ = new T2(1,_iw/* Countries.countries664 */,_it/* Countries.countries112 */),
_iy/* countries668 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Italy"));
}),
_iz/* countries669 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IT"));
}),
_iA/* countries667 */ = new T2(0,_iz/* Countries.countries669 */,_iy/* Countries.countries668 */),
_iB/* countries110 */ = new T2(1,_iA/* Countries.countries667 */,_ix/* Countries.countries111 */),
_iC/* countries671 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Israel"));
}),
_iD/* countries672 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IL"));
}),
_iE/* countries670 */ = new T2(0,_iD/* Countries.countries672 */,_iC/* Countries.countries671 */),
_iF/* countries109 */ = new T2(1,_iE/* Countries.countries670 */,_iB/* Countries.countries110 */),
_iG/* countries674 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Isle of Man"));
}),
_iH/* countries675 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IM"));
}),
_iI/* countries673 */ = new T2(0,_iH/* Countries.countries675 */,_iG/* Countries.countries674 */),
_iJ/* countries108 */ = new T2(1,_iI/* Countries.countries673 */,_iF/* Countries.countries109 */),
_iK/* countries677 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ireland"));
}),
_iL/* countries678 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IE"));
}),
_iM/* countries676 */ = new T2(0,_iL/* Countries.countries678 */,_iK/* Countries.countries677 */),
_iN/* countries107 */ = new T2(1,_iM/* Countries.countries676 */,_iJ/* Countries.countries108 */),
_iO/* countries680 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iraq"));
}),
_iP/* countries681 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IQ"));
}),
_iQ/* countries679 */ = new T2(0,_iP/* Countries.countries681 */,_iO/* Countries.countries680 */),
_iR/* countries106 */ = new T2(1,_iQ/* Countries.countries679 */,_iN/* Countries.countries107 */),
_iS/* countries683 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iran, Islamic Republic of"));
}),
_iT/* countries684 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IR"));
}),
_iU/* countries682 */ = new T2(0,_iT/* Countries.countries684 */,_iS/* Countries.countries683 */),
_iV/* countries105 */ = new T2(1,_iU/* Countries.countries682 */,_iR/* Countries.countries106 */),
_iW/* countries686 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Indonesia"));
}),
_iX/* countries687 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ID"));
}),
_iY/* countries685 */ = new T2(0,_iX/* Countries.countries687 */,_iW/* Countries.countries686 */),
_iZ/* countries104 */ = new T2(1,_iY/* Countries.countries685 */,_iV/* Countries.countries105 */),
_j0/* countries689 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("India"));
}),
_j1/* countries690 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IN"));
}),
_j2/* countries688 */ = new T2(0,_j1/* Countries.countries690 */,_j0/* Countries.countries689 */),
_j3/* countries103 */ = new T2(1,_j2/* Countries.countries688 */,_iZ/* Countries.countries104 */),
_j4/* countries692 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iceland"));
}),
_j5/* countries693 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IS"));
}),
_j6/* countries691 */ = new T2(0,_j5/* Countries.countries693 */,_j4/* Countries.countries692 */),
_j7/* countries102 */ = new T2(1,_j6/* Countries.countries691 */,_j3/* Countries.countries103 */),
_j8/* countries695 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hungary"));
}),
_j9/* countries696 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HU"));
}),
_ja/* countries694 */ = new T2(0,_j9/* Countries.countries696 */,_j8/* Countries.countries695 */),
_jb/* countries101 */ = new T2(1,_ja/* Countries.countries694 */,_j7/* Countries.countries102 */),
_jc/* countries698 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hong Kong"));
}),
_jd/* countries699 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HK"));
}),
_je/* countries697 */ = new T2(0,_jd/* Countries.countries699 */,_jc/* Countries.countries698 */),
_jf/* countries100 */ = new T2(1,_je/* Countries.countries697 */,_jb/* Countries.countries101 */),
_jg/* countries701 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Honduras"));
}),
_jh/* countries702 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HN"));
}),
_ji/* countries700 */ = new T2(0,_jh/* Countries.countries702 */,_jg/* Countries.countries701 */),
_jj/* countries99 */ = new T2(1,_ji/* Countries.countries700 */,_jf/* Countries.countries100 */),
_jk/* countries98 */ = new T2(1,_9z/* Countries.countries703 */,_jj/* Countries.countries99 */),
_jl/* countries97 */ = new T2(1,_9w/* Countries.countries706 */,_jk/* Countries.countries98 */),
_jm/* countries96 */ = new T2(1,_9t/* Countries.countries709 */,_jl/* Countries.countries97 */),
_jn/* countries95 */ = new T2(1,_9q/* Countries.countries712 */,_jm/* Countries.countries96 */),
_jo/* countries94 */ = new T2(1,_9n/* Countries.countries715 */,_jn/* Countries.countries95 */),
_jp/* countries93 */ = new T2(1,_9k/* Countries.countries718 */,_jo/* Countries.countries94 */),
_jq/* countries92 */ = new T2(1,_9h/* Countries.countries721 */,_jp/* Countries.countries93 */),
_jr/* countries91 */ = new T2(1,_9e/* Countries.countries724 */,_jq/* Countries.countries92 */),
_js/* countries90 */ = new T2(1,_9b/* Countries.countries727 */,_jr/* Countries.countries91 */),
_jt/* countries89 */ = new T2(1,_98/* Countries.countries730 */,_js/* Countries.countries90 */),
_ju/* countries88 */ = new T2(1,_95/* Countries.countries733 */,_jt/* Countries.countries89 */),
_jv/* countries87 */ = new T2(1,_92/* Countries.countries736 */,_ju/* Countries.countries88 */),
_jw/* countries86 */ = new T2(1,_8Z/* Countries.countries739 */,_jv/* Countries.countries87 */),
_jx/* countries85 */ = new T2(1,_8W/* Countries.countries742 */,_jw/* Countries.countries86 */),
_jy/* countries84 */ = new T2(1,_8T/* Countries.countries745 */,_jx/* Countries.countries85 */),
_jz/* countries83 */ = new T2(1,_8Q/* Countries.countries748 */,_jy/* Countries.countries84 */),
_jA/* countries82 */ = new T2(1,_8N/* Countries.countries751 */,_jz/* Countries.countries83 */),
_jB/* countries81 */ = new T2(1,_8K/* Countries.countries754 */,_jA/* Countries.countries82 */),
_jC/* countries80 */ = new T2(1,_8H/* Countries.countries757 */,_jB/* Countries.countries81 */),
_jD/* countries79 */ = new T2(1,_8E/* Countries.countries760 */,_jC/* Countries.countries80 */),
_jE/* countries78 */ = new T2(1,_8B/* Countries.countries763 */,_jD/* Countries.countries79 */),
_jF/* countries77 */ = new T2(1,_8y/* Countries.countries766 */,_jE/* Countries.countries78 */),
_jG/* countries76 */ = new T2(1,_8v/* Countries.countries769 */,_jF/* Countries.countries77 */),
_jH/* countries773 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finland"));
}),
_jI/* countries774 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FI"));
}),
_jJ/* countries772 */ = new T2(0,_jI/* Countries.countries774 */,_jH/* Countries.countries773 */),
_jK/* countries75 */ = new T2(1,_jJ/* Countries.countries772 */,_jG/* Countries.countries76 */),
_jL/* countries776 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Fiji"));
}),
_jM/* countries777 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FJ"));
}),
_jN/* countries775 */ = new T2(0,_jM/* Countries.countries777 */,_jL/* Countries.countries776 */),
_jO/* countries74 */ = new T2(1,_jN/* Countries.countries775 */,_jK/* Countries.countries75 */),
_jP/* countries779 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Faroe Islands"));
}),
_jQ/* countries780 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FO"));
}),
_jR/* countries778 */ = new T2(0,_jQ/* Countries.countries780 */,_jP/* Countries.countries779 */),
_jS/* countries73 */ = new T2(1,_jR/* Countries.countries778 */,_jO/* Countries.countries74 */),
_jT/* countries782 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Falkland Islands (Malvinas)"));
}),
_jU/* countries783 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FK"));
}),
_jV/* countries781 */ = new T2(0,_jU/* Countries.countries783 */,_jT/* Countries.countries782 */),
_jW/* countries72 */ = new T2(1,_jV/* Countries.countries781 */,_jS/* Countries.countries73 */),
_jX/* countries785 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ethiopia"));
}),
_jY/* countries786 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ET"));
}),
_jZ/* countries784 */ = new T2(0,_jY/* Countries.countries786 */,_jX/* Countries.countries785 */),
_k0/* countries71 */ = new T2(1,_jZ/* Countries.countries784 */,_jW/* Countries.countries72 */),
_k1/* countries788 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Estonia"));
}),
_k2/* countries789 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EE"));
}),
_k3/* countries787 */ = new T2(0,_k2/* Countries.countries789 */,_k1/* Countries.countries788 */),
_k4/* countries70 */ = new T2(1,_k3/* Countries.countries787 */,_k0/* Countries.countries71 */),
_k5/* countries791 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Eritrea"));
}),
_k6/* countries792 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ER"));
}),
_k7/* countries790 */ = new T2(0,_k6/* Countries.countries792 */,_k5/* Countries.countries791 */),
_k8/* countries69 */ = new T2(1,_k7/* Countries.countries790 */,_k4/* Countries.countries70 */),
_k9/* countries794 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Equatorial Guinea"));
}),
_ka/* countries795 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GQ"));
}),
_kb/* countries793 */ = new T2(0,_ka/* Countries.countries795 */,_k9/* Countries.countries794 */),
_kc/* countries68 */ = new T2(1,_kb/* Countries.countries793 */,_k8/* Countries.countries69 */),
_kd/* countries797 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("El Salvador"));
}),
_ke/* countries798 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SV"));
}),
_kf/* countries796 */ = new T2(0,_ke/* Countries.countries798 */,_kd/* Countries.countries797 */),
_kg/* countries67 */ = new T2(1,_kf/* Countries.countries796 */,_kc/* Countries.countries68 */),
_kh/* countries800 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Egypt"));
}),
_ki/* countries801 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EG"));
}),
_kj/* countries799 */ = new T2(0,_ki/* Countries.countries801 */,_kh/* Countries.countries800 */),
_kk/* countries66 */ = new T2(1,_kj/* Countries.countries799 */,_kg/* Countries.countries67 */),
_kl/* countries803 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ecuador"));
}),
_km/* countries804 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EC"));
}),
_kn/* countries802 */ = new T2(0,_km/* Countries.countries804 */,_kl/* Countries.countries803 */),
_ko/* countries65 */ = new T2(1,_kn/* Countries.countries802 */,_kk/* Countries.countries66 */),
_kp/* countries806 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominican Republic"));
}),
_kq/* countries807 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DO"));
}),
_kr/* countries805 */ = new T2(0,_kq/* Countries.countries807 */,_kp/* Countries.countries806 */),
_ks/* countries64 */ = new T2(1,_kr/* Countries.countries805 */,_ko/* Countries.countries65 */),
_kt/* countries809 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominica"));
}),
_ku/* countries810 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DM"));
}),
_kv/* countries808 */ = new T2(0,_ku/* Countries.countries810 */,_kt/* Countries.countries809 */),
_kw/* countries63 */ = new T2(1,_kv/* Countries.countries808 */,_ks/* Countries.countries64 */),
_kx/* countries812 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Djibouti"));
}),
_ky/* countries813 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DJ"));
}),
_kz/* countries811 */ = new T2(0,_ky/* Countries.countries813 */,_kx/* Countries.countries812 */),
_kA/* countries62 */ = new T2(1,_kz/* Countries.countries811 */,_kw/* Countries.countries63 */),
_kB/* countries815 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Denmark"));
}),
_kC/* countries816 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DK"));
}),
_kD/* countries814 */ = new T2(0,_kC/* Countries.countries816 */,_kB/* Countries.countries815 */),
_kE/* countries61 */ = new T2(1,_kD/* Countries.countries814 */,_kA/* Countries.countries62 */),
_kF/* countries818 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Czech Republic"));
}),
_kG/* countries819 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CZ"));
}),
_kH/* countries817 */ = new T2(0,_kG/* Countries.countries819 */,_kF/* Countries.countries818 */),
_kI/* countries60 */ = new T2(1,_kH/* Countries.countries817 */,_kE/* Countries.countries61 */),
_kJ/* countries821 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cyprus"));
}),
_kK/* countries822 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CY"));
}),
_kL/* countries820 */ = new T2(0,_kK/* Countries.countries822 */,_kJ/* Countries.countries821 */),
_kM/* countries59 */ = new T2(1,_kL/* Countries.countries820 */,_kI/* Countries.countries60 */),
_kN/* countries824 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cura\u00e7ao"));
}),
_kO/* countries825 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CW"));
}),
_kP/* countries823 */ = new T2(0,_kO/* Countries.countries825 */,_kN/* Countries.countries824 */),
_kQ/* countries58 */ = new T2(1,_kP/* Countries.countries823 */,_kM/* Countries.countries59 */),
_kR/* countries827 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cuba"));
}),
_kS/* countries828 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CU"));
}),
_kT/* countries826 */ = new T2(0,_kS/* Countries.countries828 */,_kR/* Countries.countries827 */),
_kU/* countries57 */ = new T2(1,_kT/* Countries.countries826 */,_kQ/* Countries.countries58 */),
_kV/* countries830 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Croatia"));
}),
_kW/* countries831 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HR"));
}),
_kX/* countries829 */ = new T2(0,_kW/* Countries.countries831 */,_kV/* Countries.countries830 */),
_kY/* countries56 */ = new T2(1,_kX/* Countries.countries829 */,_kU/* Countries.countries57 */),
_kZ/* countries833 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("C\u00f4te d\'Ivoire"));
}),
_l0/* countries834 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CI"));
}),
_l1/* countries832 */ = new T2(0,_l0/* Countries.countries834 */,_kZ/* Countries.countries833 */),
_l2/* countries55 */ = new T2(1,_l1/* Countries.countries832 */,_kY/* Countries.countries56 */),
_l3/* countries836 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Costa Rica"));
}),
_l4/* countries837 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_l5/* countries835 */ = new T2(0,_l4/* Countries.countries837 */,_l3/* Countries.countries836 */),
_l6/* countries54 */ = new T2(1,_l5/* Countries.countries835 */,_l2/* Countries.countries55 */),
_l7/* countries839 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cook Islands"));
}),
_l8/* countries840 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CK"));
}),
_l9/* countries838 */ = new T2(0,_l8/* Countries.countries840 */,_l7/* Countries.countries839 */),
_la/* countries53 */ = new T2(1,_l9/* Countries.countries838 */,_l6/* Countries.countries54 */),
_lb/* countries842 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo, the Democratic Republic of the"));
}),
_lc/* countries843 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CD"));
}),
_ld/* countries841 */ = new T2(0,_lc/* Countries.countries843 */,_lb/* Countries.countries842 */),
_le/* countries52 */ = new T2(1,_ld/* Countries.countries841 */,_la/* Countries.countries53 */),
_lf/* countries845 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo"));
}),
_lg/* countries846 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CG"));
}),
_lh/* countries844 */ = new T2(0,_lg/* Countries.countries846 */,_lf/* Countries.countries845 */),
_li/* countries51 */ = new T2(1,_lh/* Countries.countries844 */,_le/* Countries.countries52 */),
_lj/* countries848 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Comoros"));
}),
_lk/* countries849 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KM"));
}),
_ll/* countries847 */ = new T2(0,_lk/* Countries.countries849 */,_lj/* Countries.countries848 */),
_lm/* countries50 */ = new T2(1,_ll/* Countries.countries847 */,_li/* Countries.countries51 */),
_ln/* countries851 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Colombia"));
}),
_lo/* countries852 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CO"));
}),
_lp/* countries850 */ = new T2(0,_lo/* Countries.countries852 */,_ln/* Countries.countries851 */),
_lq/* countries49 */ = new T2(1,_lp/* Countries.countries850 */,_lm/* Countries.countries50 */),
_lr/* countries854 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cocos (Keeling) Islands"));
}),
_ls/* countries855 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CC"));
}),
_lt/* countries853 */ = new T2(0,_ls/* Countries.countries855 */,_lr/* Countries.countries854 */),
_lu/* countries48 */ = new T2(1,_lt/* Countries.countries853 */,_lq/* Countries.countries49 */),
_lv/* countries857 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Christmas Island"));
}),
_lw/* countries858 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CX"));
}),
_lx/* countries856 */ = new T2(0,_lw/* Countries.countries858 */,_lv/* Countries.countries857 */),
_ly/* countries47 */ = new T2(1,_lx/* Countries.countries856 */,_lu/* Countries.countries48 */),
_lz/* countries860 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("China"));
}),
_lA/* countries861 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CN"));
}),
_lB/* countries859 */ = new T2(0,_lA/* Countries.countries861 */,_lz/* Countries.countries860 */),
_lC/* countries46 */ = new T2(1,_lB/* Countries.countries859 */,_ly/* Countries.countries47 */),
_lD/* countries863 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chile"));
}),
_lE/* countries864 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CL"));
}),
_lF/* countries862 */ = new T2(0,_lE/* Countries.countries864 */,_lD/* Countries.countries863 */),
_lG/* countries45 */ = new T2(1,_lF/* Countries.countries862 */,_lC/* Countries.countries46 */),
_lH/* countries866 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chad"));
}),
_lI/* countries867 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TD"));
}),
_lJ/* countries865 */ = new T2(0,_lI/* Countries.countries867 */,_lH/* Countries.countries866 */),
_lK/* countries44 */ = new T2(1,_lJ/* Countries.countries865 */,_lG/* Countries.countries45 */),
_lL/* countries869 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Central African Republic"));
}),
_lM/* countries870 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CF"));
}),
_lN/* countries868 */ = new T2(0,_lM/* Countries.countries870 */,_lL/* Countries.countries869 */),
_lO/* countries43 */ = new T2(1,_lN/* Countries.countries868 */,_lK/* Countries.countries44 */),
_lP/* countries872 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cayman Islands"));
}),
_lQ/* countries873 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KY"));
}),
_lR/* countries871 */ = new T2(0,_lQ/* Countries.countries873 */,_lP/* Countries.countries872 */),
_lS/* countries42 */ = new T2(1,_lR/* Countries.countries871 */,_lO/* Countries.countries43 */),
_lT/* countries875 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cape Verde"));
}),
_lU/* countries876 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CV"));
}),
_lV/* countries874 */ = new T2(0,_lU/* Countries.countries876 */,_lT/* Countries.countries875 */),
_lW/* countries41 */ = new T2(1,_lV/* Countries.countries874 */,_lS/* Countries.countries42 */),
_lX/* countries878 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canada"));
}),
_lY/* countries879 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CA"));
}),
_lZ/* countries877 */ = new T2(0,_lY/* Countries.countries879 */,_lX/* Countries.countries878 */),
_m0/* countries40 */ = new T2(1,_lZ/* Countries.countries877 */,_lW/* Countries.countries41 */),
_m1/* countries881 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cameroon"));
}),
_m2/* countries882 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CM"));
}),
_m3/* countries880 */ = new T2(0,_m2/* Countries.countries882 */,_m1/* Countries.countries881 */),
_m4/* countries39 */ = new T2(1,_m3/* Countries.countries880 */,_m0/* Countries.countries40 */),
_m5/* countries884 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cambodia"));
}),
_m6/* countries885 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KH"));
}),
_m7/* countries883 */ = new T2(0,_m6/* Countries.countries885 */,_m5/* Countries.countries884 */),
_m8/* countries38 */ = new T2(1,_m7/* Countries.countries883 */,_m4/* Countries.countries39 */),
_m9/* countries887 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burundi"));
}),
_ma/* countries888 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BI"));
}),
_mb/* countries886 */ = new T2(0,_ma/* Countries.countries888 */,_m9/* Countries.countries887 */),
_mc/* countries37 */ = new T2(1,_mb/* Countries.countries886 */,_m8/* Countries.countries38 */),
_md/* countries890 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burkina Faso"));
}),
_me/* countries891 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BF"));
}),
_mf/* countries889 */ = new T2(0,_me/* Countries.countries891 */,_md/* Countries.countries890 */),
_mg/* countries36 */ = new T2(1,_mf/* Countries.countries889 */,_mc/* Countries.countries37 */),
_mh/* countries893 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bulgaria"));
}),
_mi/* countries894 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BG"));
}),
_mj/* countries892 */ = new T2(0,_mi/* Countries.countries894 */,_mh/* Countries.countries893 */),
_mk/* countries35 */ = new T2(1,_mj/* Countries.countries892 */,_mg/* Countries.countries36 */),
_ml/* countries896 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brunei Darussalam"));
}),
_mm/* countries897 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BN"));
}),
_mn/* countries895 */ = new T2(0,_mm/* Countries.countries897 */,_ml/* Countries.countries896 */),
_mo/* countries34 */ = new T2(1,_mn/* Countries.countries895 */,_mk/* Countries.countries35 */),
_mp/* countries899 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("British Indian Ocean Territory"));
}),
_mq/* countries900 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IO"));
}),
_mr/* countries898 */ = new T2(0,_mq/* Countries.countries900 */,_mp/* Countries.countries899 */),
_ms/* countries33 */ = new T2(1,_mr/* Countries.countries898 */,_mo/* Countries.countries34 */),
_mt/* countries902 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brazil"));
}),
_mu/* countries903 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BR"));
}),
_mv/* countries901 */ = new T2(0,_mu/* Countries.countries903 */,_mt/* Countries.countries902 */),
_mw/* countries32 */ = new T2(1,_mv/* Countries.countries901 */,_ms/* Countries.countries33 */),
_mx/* countries905 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bouvet Island"));
}),
_my/* countries906 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BV"));
}),
_mz/* countries904 */ = new T2(0,_my/* Countries.countries906 */,_mx/* Countries.countries905 */),
_mA/* countries31 */ = new T2(1,_mz/* Countries.countries904 */,_mw/* Countries.countries32 */),
_mB/* countries908 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Botswana"));
}),
_mC/* countries909 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BW"));
}),
_mD/* countries907 */ = new T2(0,_mC/* Countries.countries909 */,_mB/* Countries.countries908 */),
_mE/* countries30 */ = new T2(1,_mD/* Countries.countries907 */,_mA/* Countries.countries31 */),
_mF/* countries911 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bosnia and Herzegovina"));
}),
_mG/* countries912 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BA"));
}),
_mH/* countries910 */ = new T2(0,_mG/* Countries.countries912 */,_mF/* Countries.countries911 */),
_mI/* countries29 */ = new T2(1,_mH/* Countries.countries910 */,_mE/* Countries.countries30 */),
_mJ/* countries914 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bonaire, Sint Eustatius and Saba"));
}),
_mK/* countries915 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BQ"));
}),
_mL/* countries913 */ = new T2(0,_mK/* Countries.countries915 */,_mJ/* Countries.countries914 */),
_mM/* countries28 */ = new T2(1,_mL/* Countries.countries913 */,_mI/* Countries.countries29 */),
_mN/* countries917 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bolivia, Plurinational State of"));
}),
_mO/* countries918 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BO"));
}),
_mP/* countries916 */ = new T2(0,_mO/* Countries.countries918 */,_mN/* Countries.countries917 */),
_mQ/* countries27 */ = new T2(1,_mP/* Countries.countries916 */,_mM/* Countries.countries28 */),
_mR/* countries920 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bhutan"));
}),
_mS/* countries921 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BT"));
}),
_mT/* countries919 */ = new T2(0,_mS/* Countries.countries921 */,_mR/* Countries.countries920 */),
_mU/* countries26 */ = new T2(1,_mT/* Countries.countries919 */,_mQ/* Countries.countries27 */),
_mV/* countries923 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bermuda"));
}),
_mW/* countries924 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BM"));
}),
_mX/* countries922 */ = new T2(0,_mW/* Countries.countries924 */,_mV/* Countries.countries923 */),
_mY/* countries25 */ = new T2(1,_mX/* Countries.countries922 */,_mU/* Countries.countries26 */),
_mZ/* countries926 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Benin"));
}),
_n0/* countries927 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BJ"));
}),
_n1/* countries925 */ = new T2(0,_n0/* Countries.countries927 */,_mZ/* Countries.countries926 */),
_n2/* countries24 */ = new T2(1,_n1/* Countries.countries925 */,_mY/* Countries.countries25 */),
_n3/* countries929 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belize"));
}),
_n4/* countries930 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BZ"));
}),
_n5/* countries928 */ = new T2(0,_n4/* Countries.countries930 */,_n3/* Countries.countries929 */),
_n6/* countries23 */ = new T2(1,_n5/* Countries.countries928 */,_n2/* Countries.countries24 */),
_n7/* countries932 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belgium"));
}),
_n8/* countries933 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BE"));
}),
_n9/* countries931 */ = new T2(0,_n8/* Countries.countries933 */,_n7/* Countries.countries932 */),
_na/* countries22 */ = new T2(1,_n9/* Countries.countries931 */,_n6/* Countries.countries23 */),
_nb/* countries935 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belarus"));
}),
_nc/* countries936 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BY"));
}),
_nd/* countries934 */ = new T2(0,_nc/* Countries.countries936 */,_nb/* Countries.countries935 */),
_ne/* countries21 */ = new T2(1,_nd/* Countries.countries934 */,_na/* Countries.countries22 */),
_nf/* countries938 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Barbados"));
}),
_ng/* countries939 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BB"));
}),
_nh/* countries937 */ = new T2(0,_ng/* Countries.countries939 */,_nf/* Countries.countries938 */),
_ni/* countries20 */ = new T2(1,_nh/* Countries.countries937 */,_ne/* Countries.countries21 */),
_nj/* countries941 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bangladesh"));
}),
_nk/* countries942 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BD"));
}),
_nl/* countries940 */ = new T2(0,_nk/* Countries.countries942 */,_nj/* Countries.countries941 */),
_nm/* countries19 */ = new T2(1,_nl/* Countries.countries940 */,_ni/* Countries.countries20 */),
_nn/* countries944 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahrain"));
}),
_no/* countries945 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BH"));
}),
_np/* countries943 */ = new T2(0,_no/* Countries.countries945 */,_nn/* Countries.countries944 */),
_nq/* countries18 */ = new T2(1,_np/* Countries.countries943 */,_nm/* Countries.countries19 */),
_nr/* countries947 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahamas"));
}),
_ns/* countries948 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_nt/* countries946 */ = new T2(0,_ns/* Countries.countries948 */,_nr/* Countries.countries947 */),
_nu/* countries17 */ = new T2(1,_nt/* Countries.countries946 */,_nq/* Countries.countries18 */),
_nv/* countries950 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Azerbaijan"));
}),
_nw/* countries951 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AZ"));
}),
_nx/* countries949 */ = new T2(0,_nw/* Countries.countries951 */,_nv/* Countries.countries950 */),
_ny/* countries16 */ = new T2(1,_nx/* Countries.countries949 */,_nu/* Countries.countries17 */),
_nz/* countries953 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Austria"));
}),
_nA/* countries954 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AT"));
}),
_nB/* countries952 */ = new T2(0,_nA/* Countries.countries954 */,_nz/* Countries.countries953 */),
_nC/* countries15 */ = new T2(1,_nB/* Countries.countries952 */,_ny/* Countries.countries16 */),
_nD/* countries956 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Australia"));
}),
_nE/* countries957 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AU"));
}),
_nF/* countries955 */ = new T2(0,_nE/* Countries.countries957 */,_nD/* Countries.countries956 */),
_nG/* countries14 */ = new T2(1,_nF/* Countries.countries955 */,_nC/* Countries.countries15 */),
_nH/* countries959 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Aruba"));
}),
_nI/* countries960 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AW"));
}),
_nJ/* countries958 */ = new T2(0,_nI/* Countries.countries960 */,_nH/* Countries.countries959 */),
_nK/* countries13 */ = new T2(1,_nJ/* Countries.countries958 */,_nG/* Countries.countries14 */),
_nL/* countries962 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Armenia"));
}),
_nM/* countries963 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AM"));
}),
_nN/* countries961 */ = new T2(0,_nM/* Countries.countries963 */,_nL/* Countries.countries962 */),
_nO/* countries12 */ = new T2(1,_nN/* Countries.countries961 */,_nK/* Countries.countries13 */),
_nP/* countries965 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Argentina"));
}),
_nQ/* countries966 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AR"));
}),
_nR/* countries964 */ = new T2(0,_nQ/* Countries.countries966 */,_nP/* Countries.countries965 */),
_nS/* countries11 */ = new T2(1,_nR/* Countries.countries964 */,_nO/* Countries.countries12 */),
_nT/* countries968 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antigua and Barbuda"));
}),
_nU/* countries969 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AG"));
}),
_nV/* countries967 */ = new T2(0,_nU/* Countries.countries969 */,_nT/* Countries.countries968 */),
_nW/* countries10 */ = new T2(1,_nV/* Countries.countries967 */,_nS/* Countries.countries11 */),
_nX/* countries971 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antarctica"));
}),
_nY/* countries972 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AQ"));
}),
_nZ/* countries970 */ = new T2(0,_nY/* Countries.countries972 */,_nX/* Countries.countries971 */),
_o0/* countries9 */ = new T2(1,_nZ/* Countries.countries970 */,_nW/* Countries.countries10 */),
_o1/* countries974 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Anguilla"));
}),
_o2/* countries975 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AI"));
}),
_o3/* countries973 */ = new T2(0,_o2/* Countries.countries975 */,_o1/* Countries.countries974 */),
_o4/* countries8 */ = new T2(1,_o3/* Countries.countries973 */,_o0/* Countries.countries9 */),
_o5/* countries977 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Angola"));
}),
_o6/* countries978 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AO"));
}),
_o7/* countries976 */ = new T2(0,_o6/* Countries.countries978 */,_o5/* Countries.countries977 */),
_o8/* countries7 */ = new T2(1,_o7/* Countries.countries976 */,_o4/* Countries.countries8 */),
_o9/* countries980 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Andorra"));
}),
_oa/* countries981 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AD"));
}),
_ob/* countries979 */ = new T2(0,_oa/* Countries.countries981 */,_o9/* Countries.countries980 */),
_oc/* countries6 */ = new T2(1,_ob/* Countries.countries979 */,_o8/* Countries.countries7 */),
_od/* countries983 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("American Samoa"));
}),
_oe/* countries984 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AS"));
}),
_of/* countries982 */ = new T2(0,_oe/* Countries.countries984 */,_od/* Countries.countries983 */),
_og/* countries5 */ = new T2(1,_of/* Countries.countries982 */,_oc/* Countries.countries6 */),
_oh/* countries986 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Algeria"));
}),
_oi/* countries987 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DZ"));
}),
_oj/* countries985 */ = new T2(0,_oi/* Countries.countries987 */,_oh/* Countries.countries986 */),
_ok/* countries4 */ = new T2(1,_oj/* Countries.countries985 */,_og/* Countries.countries5 */),
_ol/* countries989 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Albania"));
}),
_om/* countries990 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AL"));
}),
_on/* countries988 */ = new T2(0,_om/* Countries.countries990 */,_ol/* Countries.countries989 */),
_oo/* countries3 */ = new T2(1,_on/* Countries.countries988 */,_ok/* Countries.countries4 */),
_op/* countries992 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u00c5land Islands"));
}),
_oq/* countries993 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AX"));
}),
_or/* countries991 */ = new T2(0,_oq/* Countries.countries993 */,_op/* Countries.countries992 */),
_os/* countries2 */ = new T2(1,_or/* Countries.countries991 */,_oo/* Countries.countries3 */),
_ot/* countries995 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Afghanistan"));
}),
_ou/* countries996 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AF"));
}),
_ov/* countries994 */ = new T2(0,_ou/* Countries.countries996 */,_ot/* Countries.countries995 */),
_ow/* countries1 */ = new T2(1,_ov/* Countries.countries994 */,_os/* Countries.countries2 */),
_ox/* countries998 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("--select--"));
}),
_oy/* countries997 */ = new T2(0,_I/* GHC.Types.[] */,_ox/* Countries.countries998 */),
_oz/* countries */ = new T2(1,_oy/* Countries.countries997 */,_ow/* Countries.countries1 */),
_oA/* ch0GeneralInformation33 */ = new T2(5,_8s/* FormStructure.Chapter0.ch0GeneralInformation34 */,_oz/* Countries.countries */),
_oB/* ch0GeneralInformation32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institution name"));
}),
_oC/* ch0GeneralInformation31 */ = new T1(1,_oB/* FormStructure.Chapter0.ch0GeneralInformation32 */),
_oD/* ch0GeneralInformation30 */ = {_:0,a:_oC/* FormStructure.Chapter0.ch0GeneralInformation31 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_oE/* ch0GeneralInformation29 */ = new T1(0,_oD/* FormStructure.Chapter0.ch0GeneralInformation30 */),
_oF/* ch0GeneralInformation28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Organisation unit"));
}),
_oG/* ch0GeneralInformation27 */ = new T1(1,_oF/* FormStructure.Chapter0.ch0GeneralInformation28 */),
_oH/* ch0GeneralInformation26 */ = {_:0,a:_oG/* FormStructure.Chapter0.ch0GeneralInformation27 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_oI/* ch0GeneralInformation25 */ = new T1(0,_oH/* FormStructure.Chapter0.ch0GeneralInformation26 */),
_oJ/* ch0GeneralInformation15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("research group"));
}),
_oK/* ch0GeneralInformation14 */ = new T1(0,_oJ/* FormStructure.Chapter0.ch0GeneralInformation15 */),
_oL/* ch0GeneralInformation13 */ = new T2(1,_oK/* FormStructure.Chapter0.ch0GeneralInformation14 */,_I/* GHC.Types.[] */),
_oM/* ch0GeneralInformation17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("department"));
}),
_oN/* ch0GeneralInformation16 */ = new T1(0,_oM/* FormStructure.Chapter0.ch0GeneralInformation17 */),
_oO/* ch0GeneralInformation12 */ = new T2(1,_oN/* FormStructure.Chapter0.ch0GeneralInformation16 */,_oL/* FormStructure.Chapter0.ch0GeneralInformation13 */),
_oP/* ch0GeneralInformation19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("faculty"));
}),
_oQ/* ch0GeneralInformation18 */ = new T1(0,_oP/* FormStructure.Chapter0.ch0GeneralInformation19 */),
_oR/* ch0GeneralInformation11 */ = new T2(1,_oQ/* FormStructure.Chapter0.ch0GeneralInformation18 */,_oO/* FormStructure.Chapter0.ch0GeneralInformation12 */),
_oS/* ch0GeneralInformation21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution"));
}),
_oT/* ch0GeneralInformation20 */ = new T1(0,_oS/* FormStructure.Chapter0.ch0GeneralInformation21 */),
_oU/* ch0GeneralInformation10 */ = new T2(1,_oT/* FormStructure.Chapter0.ch0GeneralInformation20 */,_oR/* FormStructure.Chapter0.ch0GeneralInformation11 */),
_oV/* ch0GeneralInformation24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Level of unit"));
}),
_oW/* ch0GeneralInformation23 */ = new T1(1,_oV/* FormStructure.Chapter0.ch0GeneralInformation24 */),
_oX/* ch0GeneralInformation22 */ = {_:0,a:_oW/* FormStructure.Chapter0.ch0GeneralInformation23 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_oY/* ch0GeneralInformation9 */ = new T2(4,_oX/* FormStructure.Chapter0.ch0GeneralInformation22 */,_oU/* FormStructure.Chapter0.ch0GeneralInformation10 */),
_oZ/* ch0GeneralInformation8 */ = new T2(1,_oY/* FormStructure.Chapter0.ch0GeneralInformation9 */,_I/* GHC.Types.[] */),
_p0/* ch0GeneralInformation7 */ = new T2(1,_oI/* FormStructure.Chapter0.ch0GeneralInformation25 */,_oZ/* FormStructure.Chapter0.ch0GeneralInformation8 */),
_p1/* ch0GeneralInformation6 */ = new T2(1,_oE/* FormStructure.Chapter0.ch0GeneralInformation29 */,_p0/* FormStructure.Chapter0.ch0GeneralInformation7 */),
_p2/* ch0GeneralInformation5 */ = new T2(1,_oA/* FormStructure.Chapter0.ch0GeneralInformation33 */,_p1/* FormStructure.Chapter0.ch0GeneralInformation6 */),
_p3/* ch0GeneralInformation4 */ = new T3(7,_8p/* FormStructure.Chapter0.ch0GeneralInformation38 */,_8m/* FormStructure.Chapter0.ch0GeneralInformation37 */,_p2/* FormStructure.Chapter0.ch0GeneralInformation5 */),
_p4/* ch0GeneralInformation2 */ = new T2(1,_p3/* FormStructure.Chapter0.ch0GeneralInformation4 */,_8l/* FormStructure.Chapter0.ch0GeneralInformation3 */),
_p5/* ch0GeneralInformation48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Email"));
}),
_p6/* ch0GeneralInformation47 */ = new T1(1,_p5/* FormStructure.Chapter0.ch0GeneralInformation48 */),
_p7/* ch0GeneralInformation46 */ = {_:0,a:_p6/* FormStructure.Chapter0.ch0GeneralInformation47 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_p8/* ch0GeneralInformation45 */ = new T1(2,_p7/* FormStructure.Chapter0.ch0GeneralInformation46 */),
_p9/* ch0GeneralInformation44 */ = new T2(1,_p8/* FormStructure.Chapter0.ch0GeneralInformation45 */,_I/* GHC.Types.[] */),
_pa/* ch0GeneralInformation52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Surname"));
}),
_pb/* ch0GeneralInformation51 */ = new T1(1,_pa/* FormStructure.Chapter0.ch0GeneralInformation52 */),
_pc/* ch0GeneralInformation50 */ = {_:0,a:_pb/* FormStructure.Chapter0.ch0GeneralInformation51 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pd/* ch0GeneralInformation49 */ = new T1(0,_pc/* FormStructure.Chapter0.ch0GeneralInformation50 */),
_pe/* ch0GeneralInformation43 */ = new T2(1,_pd/* FormStructure.Chapter0.ch0GeneralInformation49 */,_p9/* FormStructure.Chapter0.ch0GeneralInformation44 */),
_pf/* ch0GeneralInformation56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("First name"));
}),
_pg/* ch0GeneralInformation55 */ = new T1(1,_pf/* FormStructure.Chapter0.ch0GeneralInformation56 */),
_ph/* ch0GeneralInformation54 */ = {_:0,a:_pg/* FormStructure.Chapter0.ch0GeneralInformation55 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_pi/* ch0GeneralInformation53 */ = new T1(0,_ph/* FormStructure.Chapter0.ch0GeneralInformation54 */),
_pj/* ch0GeneralInformation42 */ = new T2(1,_pi/* FormStructure.Chapter0.ch0GeneralInformation53 */,_pe/* FormStructure.Chapter0.ch0GeneralInformation43 */),
_pk/* ch0GeneralInformation59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Registration of the responder"));
}),
_pl/* ch0GeneralInformation58 */ = new T1(1,_pk/* FormStructure.Chapter0.ch0GeneralInformation59 */),
_pm/* ch0GeneralInformation57 */ = {_:0,a:_pl/* FormStructure.Chapter0.ch0GeneralInformation58 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pn/* ch0GeneralInformation41 */ = new T3(7,_pm/* FormStructure.Chapter0.ch0GeneralInformation57 */,_8m/* FormStructure.Chapter0.ch0GeneralInformation37 */,_pj/* FormStructure.Chapter0.ch0GeneralInformation42 */),
_po/* ch0GeneralInformation1 */ = new T2(1,_pn/* FormStructure.Chapter0.ch0GeneralInformation41 */,_p4/* FormStructure.Chapter0.ch0GeneralInformation2 */),
_pp/* ch0GeneralInformation62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("0.General Info"));
}),
_pq/* ch0GeneralInformation61 */ = new T1(1,_pp/* FormStructure.Chapter0.ch0GeneralInformation62 */),
_pr/* ch0GeneralInformation60 */ = {_:0,a:_pq/* FormStructure.Chapter0.ch0GeneralInformation61 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_ps/* ch0GeneralInformation */ = new T2(6,_pr/* FormStructure.Chapter0.ch0GeneralInformation60 */,_po/* FormStructure.Chapter0.ch0GeneralInformation1 */),
_pt/* ch1DataProduction226 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you produce raw data?"));
}),
_pu/* ch1DataProduction225 */ = new T1(1,_pt/* FormStructure.Chapter1.ch1DataProduction226 */),
_pv/* ch1DataProduction224 */ = {_:0,a:_pu/* FormStructure.Chapter1.ch1DataProduction225 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_pw/* ch1DataProduction6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_px/* ch1DataProduction5 */ = new T1(0,_pw/* FormStructure.Chapter1.ch1DataProduction6 */),
_py/* ch1DataProduction4 */ = new T2(1,_px/* FormStructure.Chapter1.ch1DataProduction5 */,_I/* GHC.Types.[] */),
_pz/* ch1DataProduction223 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_pA/* ch1DataProduction123 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_pB/* ch1DataProduction122 */ = new T1(0,_pA/* FormStructure.Chapter1.ch1DataProduction123 */),
_pC/* ReadOnlyRule */ = new T0(3),
_pD/* ch1DataProduction125 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_pE/* ch1DataProduction127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-sum"));
}),
_pF/* ch1DataProduction126 */ = new T1(1,_pE/* FormStructure.Chapter1.ch1DataProduction127 */),
_pG/* ch1DataProduction129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production cost"));
}),
_pH/* ch1DataProduction128 */ = new T1(1,_pG/* FormStructure.Chapter1.ch1DataProduction129 */),
_pI/* ch1DataProduction124 */ = {_:0,a:_pH/* FormStructure.Chapter1.ch1DataProduction128 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_pF/* FormStructure.Chapter1.ch1DataProduction126 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_pD/* FormStructure.Chapter1.ch1DataProduction125 */},
_pJ/* ch1DataProduction121 */ = new T2(3,_pI/* FormStructure.Chapter1.ch1DataProduction124 */,_pB/* FormStructure.Chapter1.ch1DataProduction122 */),
_pK/* ch1DataProduction120 */ = new T2(1,_pJ/* FormStructure.Chapter1.ch1DataProduction121 */,_I/* GHC.Types.[] */),
_pL/* ch1DataProduction132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_pM/* ch1DataProduction131 */ = new T1(0,_pL/* FormStructure.Chapter1.ch1DataProduction132 */),
_pN/* totalSum1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_pO/* totalSum11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_pP/* totalSum10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_pQ/* totalSum7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_pR/* totalSum6 */ = new T2(1,_pQ/* FormStructure.Common.totalSum7 */,_I/* GHC.Types.[] */),
_pS/* totalSum8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_pT/* totalSum5 */ = new T2(1,_pS/* FormStructure.Common.totalSum8 */,_pR/* FormStructure.Common.totalSum6 */),
_pU/* totalSum9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_pV/* totalSum4 */ = new T2(1,_pU/* FormStructure.Common.totalSum9 */,_pT/* FormStructure.Common.totalSum5 */),
_pW/* totalSum3 */ = new T2(1,_pP/* FormStructure.Common.totalSum10 */,_pV/* FormStructure.Common.totalSum4 */),
_pX/* totalSum2 */ = new T2(1,_pO/* FormStructure.Common.totalSum11 */,_pW/* FormStructure.Common.totalSum3 */),
_pY/* totalSum */ = new T2(1,_pX/* FormStructure.Common.totalSum2 */,_pN/* FormStructure.Common.totalSum1 */),
_pZ/* ch1DataProduction135 */ = new T2(1,_pY/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_q0/* ch1DataProduction134 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_pZ/* FormStructure.Chapter1.ch1DataProduction135 */),
_q1/* ch1DataProduction137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-sum"));
}),
_q2/* ch1DataProduction136 */ = new T1(1,_q1/* FormStructure.Chapter1.ch1DataProduction137 */),
_q3/* ch1DataProduction139 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production volume"));
}),
_q4/* ch1DataProduction138 */ = new T1(1,_q3/* FormStructure.Chapter1.ch1DataProduction139 */),
_q5/* ch1DataProduction133 */ = {_:0,a:_q4/* FormStructure.Chapter1.ch1DataProduction138 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_q2/* FormStructure.Chapter1.ch1DataProduction136 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_q0/* FormStructure.Chapter1.ch1DataProduction134 */},
_q6/* ch1DataProduction130 */ = new T2(3,_q5/* FormStructure.Chapter1.ch1DataProduction133 */,_pM/* FormStructure.Chapter1.ch1DataProduction131 */),
_q7/* ch1DataProduction119 */ = new T2(1,_q6/* FormStructure.Chapter1.ch1DataProduction130 */,_pK/* FormStructure.Chapter1.ch1DataProduction120 */),
_q8/* ch1DataProduction150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-others"));
}),
_q9/* ch1DataProduction149 */ = new T2(1,_q8/* FormStructure.Chapter1.ch1DataProduction150 */,_I/* GHC.Types.[] */),
_qa/* ch1DataProduction151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-proteomics"));
}),
_qb/* ch1DataProduction148 */ = new T2(1,_qa/* FormStructure.Chapter1.ch1DataProduction151 */,_q9/* FormStructure.Chapter1.ch1DataProduction149 */),
_qc/* ch1DataProduction152 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-genomics"));
}),
_qd/* ch1DataProduction147 */ = new T2(1,_qc/* FormStructure.Chapter1.ch1DataProduction152 */,_qb/* FormStructure.Chapter1.ch1DataProduction148 */),
_qe/* ch1DataProduction_costSumRule */ = new T2(0,_qd/* FormStructure.Chapter1.ch1DataProduction147 */,_pE/* FormStructure.Chapter1.ch1DataProduction127 */),
_qf/* ch1DataProduction146 */ = new T2(1,_qe/* FormStructure.Chapter1.ch1DataProduction_costSumRule */,_I/* GHC.Types.[] */),
_qg/* ch1DataProduction154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_qh/* ch1DataProduction153 */ = new T1(1,_qg/* FormStructure.Chapter1.ch1DataProduction154 */),
_qi/* ch1DataProduction155 */ = new T1(1,_q8/* FormStructure.Chapter1.ch1DataProduction150 */),
_qj/* ch1DataProduction157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost for year 2015"));
}),
_qk/* ch1DataProduction156 */ = new T1(1,_qj/* FormStructure.Chapter1.ch1DataProduction157 */),
_ql/* ch1DataProduction145 */ = {_:0,a:_qk/* FormStructure.Chapter1.ch1DataProduction156 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_qi/* FormStructure.Chapter1.ch1DataProduction155 */,d:_I/* GHC.Types.[] */,e:_qh/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qf/* FormStructure.Chapter1.ch1DataProduction146 */},
_qm/* ch1DataProduction144 */ = new T2(3,_ql/* FormStructure.Chapter1.ch1DataProduction145 */,_pB/* FormStructure.Chapter1.ch1DataProduction122 */),
_qn/* ch1DataProduction143 */ = new T2(1,_qm/* FormStructure.Chapter1.ch1DataProduction144 */,_I/* GHC.Types.[] */),
_qo/* ch1DataProduction164 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_qp/* ch1DataProduction163 */ = new T2(1,_qo/* FormStructure.Chapter1.ch1DataProduction164 */,_I/* GHC.Types.[] */),
_qq/* ch1DataProduction162 */ = new T2(1,_pL/* FormStructure.Chapter1.ch1DataProduction132 */,_qp/* FormStructure.Chapter1.ch1DataProduction163 */),
_qr/* ch1DataProduction165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_qs/* ch1DataProduction161 */ = new T2(1,_qr/* FormStructure.Chapter1.ch1DataProduction165 */,_qq/* FormStructure.Chapter1.ch1DataProduction162 */),
_qt/* ch1DataProduction166 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_qu/* ch1DataProduction160 */ = new T2(1,_qt/* FormStructure.Chapter1.ch1DataProduction166 */,_qs/* FormStructure.Chapter1.ch1DataProduction161 */),
_qv/* ch1DataProduction159 */ = new T1(1,_qu/* FormStructure.Chapter1.ch1DataProduction160 */),
_qw/* ch1DataProduction180 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_qx/* ch1DataProduction179 */ = new T2(1,_qw/* FormStructure.Chapter1.ch1DataProduction180 */,_I/* GHC.Types.[] */),
_qy/* ch1DataProduction181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_qz/* ch1DataProduction178 */ = new T2(1,_qy/* FormStructure.Chapter1.ch1DataProduction181 */,_qx/* FormStructure.Chapter1.ch1DataProduction179 */),
_qA/* ch1DataProduction175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_qB/* ch1DataProduction182 */ = new T1(1,_qA/* FormStructure.Chapter1.ch1DataProduction175 */),
_qC/* ch1DataProduction184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Volume"));
}),
_qD/* ch1DataProduction183 */ = new T1(1,_qC/* FormStructure.Chapter1.ch1DataProduction184 */),
_qE/* ch1DataProduction170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_qF/* ch1DataProduction169 */ = new T2(2,_q1/* FormStructure.Chapter1.ch1DataProduction137 */,_qE/* FormStructure.Chapter1.ch1DataProduction170 */),
_qG/* ch1DataProduction168 */ = new T2(1,_qF/* FormStructure.Chapter1.ch1DataProduction169 */,_I/* GHC.Types.[] */),
_qH/* ch1DataProduction174 */ = new T2(1,_qA/* FormStructure.Chapter1.ch1DataProduction175 */,_I/* GHC.Types.[] */),
_qI/* ch1DataProduction176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_qJ/* ch1DataProduction173 */ = new T2(1,_qI/* FormStructure.Chapter1.ch1DataProduction176 */,_qH/* FormStructure.Chapter1.ch1DataProduction174 */),
_qK/* ch1DataProduction177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_qL/* ch1DataProduction172 */ = new T2(1,_qK/* FormStructure.Chapter1.ch1DataProduction177 */,_qJ/* FormStructure.Chapter1.ch1DataProduction173 */),
_qM/* ch1DataProduction171 */ = new T2(1,_qL/* FormStructure.Chapter1.ch1DataProduction172 */,_q1/* FormStructure.Chapter1.ch1DataProduction137 */),
_qN/* ch1DataProduction_volumeSumRules */ = new T2(1,_qM/* FormStructure.Chapter1.ch1DataProduction171 */,_qG/* FormStructure.Chapter1.ch1DataProduction168 */),
_qO/* ch1DataProduction167 */ = {_:0,a:_qD/* FormStructure.Chapter1.ch1DataProduction183 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_qB/* FormStructure.Chapter1.ch1DataProduction182 */,d:_qz/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_qN/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_qP/* ch1DataProduction158 */ = new T2(3,_qO/* FormStructure.Chapter1.ch1DataProduction167 */,_qv/* FormStructure.Chapter1.ch1DataProduction159 */),
_qQ/* ch1DataProduction142 */ = new T2(1,_qP/* FormStructure.Chapter1.ch1DataProduction158 */,_qn/* FormStructure.Chapter1.ch1DataProduction143 */),
_qR/* ch1DataProduction188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Images, chips, spectra, ..."));
}),
_qS/* ch1DataProduction187 */ = new T1(1,_qR/* FormStructure.Chapter1.ch1DataProduction188 */),
_qT/* ch1DataProduction190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Specify the output type of raw data"));
}),
_qU/* ch1DataProduction189 */ = new T1(1,_qT/* FormStructure.Chapter1.ch1DataProduction190 */),
_qV/* ch1DataProduction186 */ = {_:0,a:_qU/* FormStructure.Chapter1.ch1DataProduction189 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_qS/* FormStructure.Chapter1.ch1DataProduction187 */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_qW/* ch1DataProduction185 */ = new T1(0,_qV/* FormStructure.Chapter1.ch1DataProduction186 */),
_qX/* ch1DataProduction141 */ = new T2(1,_qW/* FormStructure.Chapter1.ch1DataProduction185 */,_qQ/* FormStructure.Chapter1.ch1DataProduction142 */),
_qY/* ch1DataProduction193 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Others"));
}),
_qZ/* ch1DataProduction192 */ = new T1(1,_qY/* FormStructure.Chapter1.ch1DataProduction193 */),
_r0/* ch1DataProduction191 */ = {_:0,a:_qZ/* FormStructure.Chapter1.ch1DataProduction192 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_r1/* ch1DataProduction67 */ = 0,
_r2/* ch1DataProduction140 */ = new T3(8,_r0/* FormStructure.Chapter1.ch1DataProduction191 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_qX/* FormStructure.Chapter1.ch1DataProduction141 */),
_r3/* ch1DataProduction118 */ = new T2(1,_r2/* FormStructure.Chapter1.ch1DataProduction140 */,_q7/* FormStructure.Chapter1.ch1DataProduction119 */),
_r4/* ch1DataProduction199 */ = new T1(1,_qa/* FormStructure.Chapter1.ch1DataProduction151 */),
_r5/* ch1DataProduction198 */ = {_:0,a:_qk/* FormStructure.Chapter1.ch1DataProduction156 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_r4/* FormStructure.Chapter1.ch1DataProduction199 */,d:_I/* GHC.Types.[] */,e:_qh/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qf/* FormStructure.Chapter1.ch1DataProduction146 */},
_r6/* ch1DataProduction197 */ = new T2(3,_r5/* FormStructure.Chapter1.ch1DataProduction198 */,_pB/* FormStructure.Chapter1.ch1DataProduction122 */),
_r7/* ch1DataProduction196 */ = new T2(1,_r6/* FormStructure.Chapter1.ch1DataProduction197 */,_I/* GHC.Types.[] */),
_r8/* ch1DataProduction202 */ = new T1(1,_qI/* FormStructure.Chapter1.ch1DataProduction176 */),
_r9/* ch1DataProduction201 */ = {_:0,a:_qD/* FormStructure.Chapter1.ch1DataProduction183 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_r8/* FormStructure.Chapter1.ch1DataProduction202 */,d:_qz/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_qN/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_ra/* ch1DataProduction200 */ = new T2(3,_r9/* FormStructure.Chapter1.ch1DataProduction201 */,_qv/* FormStructure.Chapter1.ch1DataProduction159 */),
_rb/* ch1DataProduction195 */ = new T2(1,_ra/* FormStructure.Chapter1.ch1DataProduction200 */,_r7/* FormStructure.Chapter1.ch1DataProduction196 */),
_rc/* ch1DataProduction205 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Proteomics"));
}),
_rd/* ch1DataProduction204 */ = new T1(1,_rc/* FormStructure.Chapter1.ch1DataProduction205 */),
_re/* ch1DataProduction203 */ = {_:0,a:_rd/* FormStructure.Chapter1.ch1DataProduction204 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rf/* ch1DataProduction194 */ = new T3(8,_re/* FormStructure.Chapter1.ch1DataProduction203 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_rb/* FormStructure.Chapter1.ch1DataProduction195 */),
_rg/* ch1DataProduction117 */ = new T2(1,_rf/* FormStructure.Chapter1.ch1DataProduction194 */,_r3/* FormStructure.Chapter1.ch1DataProduction118 */),
_rh/* ch1DataProduction211 */ = new T1(1,_qc/* FormStructure.Chapter1.ch1DataProduction152 */),
_ri/* ch1DataProduction210 */ = {_:0,a:_qk/* FormStructure.Chapter1.ch1DataProduction156 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_rh/* FormStructure.Chapter1.ch1DataProduction211 */,d:_I/* GHC.Types.[] */,e:_qh/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_qf/* FormStructure.Chapter1.ch1DataProduction146 */},
_rj/* ch1DataProduction209 */ = new T2(3,_ri/* FormStructure.Chapter1.ch1DataProduction210 */,_pB/* FormStructure.Chapter1.ch1DataProduction122 */),
_rk/* ch1DataProduction208 */ = new T2(1,_rj/* FormStructure.Chapter1.ch1DataProduction209 */,_I/* GHC.Types.[] */),
_rl/* ch1DataProduction214 */ = new T1(1,_qK/* FormStructure.Chapter1.ch1DataProduction177 */),
_rm/* ch1DataProduction213 */ = {_:0,a:_qD/* FormStructure.Chapter1.ch1DataProduction183 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_rl/* FormStructure.Chapter1.ch1DataProduction214 */,d:_qz/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_qN/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_rn/* ch1DataProduction212 */ = new T2(3,_rm/* FormStructure.Chapter1.ch1DataProduction213 */,_qv/* FormStructure.Chapter1.ch1DataProduction159 */),
_ro/* ch1DataProduction207 */ = new T2(1,_rn/* FormStructure.Chapter1.ch1DataProduction212 */,_rk/* FormStructure.Chapter1.ch1DataProduction208 */),
_rp/* ch1DataProduction217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Genomics"));
}),
_rq/* ch1DataProduction216 */ = new T1(1,_rp/* FormStructure.Chapter1.ch1DataProduction217 */),
_rr/* ch1DataProduction215 */ = {_:0,a:_rq/* FormStructure.Chapter1.ch1DataProduction216 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rs/* ch1DataProduction206 */ = new T3(8,_rr/* FormStructure.Chapter1.ch1DataProduction215 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_ro/* FormStructure.Chapter1.ch1DataProduction207 */),
_rt/* ch1DataProduction116 */ = new T2(1,_rs/* FormStructure.Chapter1.ch1DataProduction206 */,_rg/* FormStructure.Chapter1.ch1DataProduction117 */),
_ru/* ch1DataProduction220 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(Estimated) volume of raw data produced inhouse in 2015"));
}),
_rv/* ch1DataProduction219 */ = new T1(1,_ru/* FormStructure.Chapter1.ch1DataProduction220 */),
_rw/* ch1DataProduction222 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Type of data"));
}),
_rx/* ch1DataProduction221 */ = new T1(1,_rw/* FormStructure.Chapter1.ch1DataProduction222 */),
_ry/* ch1DataProduction218 */ = {_:0,a:_rx/* FormStructure.Chapter1.ch1DataProduction221 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_rv/* FormStructure.Chapter1.ch1DataProduction219 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rz/* ch1DataProduction115 */ = new T3(7,_ry/* FormStructure.Chapter1.ch1DataProduction218 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_rt/* FormStructure.Chapter1.ch1DataProduction116 */),
_rA/* ch1DataProduction11 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_rB/* ch1DataProduction19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_rC/* ch1DataProduction18 */ = new T1(0,_rB/* FormStructure.Chapter1.ch1DataProduction19 */),
_rD/* ch1DataProduction24 */ = function(_rE/* scfW */){
  return (E(_rE/* scfW */)==100) ? true : false;
},
_rF/* ch1DataProduction23 */ = new T1(4,_rD/* FormStructure.Chapter1.ch1DataProduction24 */),
_rG/* ch1DataProduction22 */ = new T2(1,_rF/* FormStructure.Chapter1.ch1DataProduction23 */,_I/* GHC.Types.[] */),
_rH/* ch1DataProduction21 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_rG/* FormStructure.Chapter1.ch1DataProduction22 */),
_rI/* ch1DataProduction26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-sum"));
}),
_rJ/* ch1DataProduction25 */ = new T1(1,_rI/* FormStructure.Chapter1.ch1DataProduction26 */),
_rK/* ch1DataProduction28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_rL/* ch1DataProduction27 */ = new T1(1,_rK/* FormStructure.Chapter1.ch1DataProduction28 */),
_rM/* ch1DataProduction20 */ = {_:0,a:_rL/* FormStructure.Chapter1.ch1DataProduction27 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_rJ/* FormStructure.Chapter1.ch1DataProduction25 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_rH/* FormStructure.Chapter1.ch1DataProduction21 */},
_rN/* ch1DataProduction17 */ = new T2(3,_rM/* FormStructure.Chapter1.ch1DataProduction20 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_rO/* ch1DataProduction16 */ = new T2(1,_rN/* FormStructure.Chapter1.ch1DataProduction17 */,_I/* GHC.Types.[] */),
_rP/* ch1DataProduction34 */ = function(_rQ/* scfQ */){
  var _rR/* scfR */ = E(_rQ/* scfQ */);
  return (_rR/* scfR */<0) ? false : _rR/* scfR */<=100;
},
_rS/* ch1DataProduction33 */ = new T1(4,_rP/* FormStructure.Chapter1.ch1DataProduction34 */),
_rT/* ch1DataProduction32 */ = new T2(1,_rS/* FormStructure.Chapter1.ch1DataProduction33 */,_I/* GHC.Types.[] */),
_rU/* ch1DataProduction38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-open"));
}),
_rV/* ch1DataProduction37 */ = new T2(1,_rU/* FormStructure.Chapter1.ch1DataProduction38 */,_I/* GHC.Types.[] */),
_rW/* ch1DataProduction39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-closed"));
}),
_rX/* ch1DataProduction36 */ = new T2(1,_rW/* FormStructure.Chapter1.ch1DataProduction39 */,_rV/* FormStructure.Chapter1.ch1DataProduction37 */),
_rY/* ch1DataProduction40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-inside"));
}),
_rZ/* ch1DataProduction35 */ = new T2(1,_rY/* FormStructure.Chapter1.ch1DataProduction40 */,_rX/* FormStructure.Chapter1.ch1DataProduction36 */),
_s0/* ch1DataProduction_accSumRule */ = new T2(0,_rZ/* FormStructure.Chapter1.ch1DataProduction35 */,_rI/* FormStructure.Chapter1.ch1DataProduction26 */),
_s1/* ch1DataProduction31 */ = new T2(1,_s0/* FormStructure.Chapter1.ch1DataProduction_accSumRule */,_rT/* FormStructure.Chapter1.ch1DataProduction32 */),
_s2/* ch1DataProduction42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_s3/* ch1DataProduction41 */ = new T1(1,_s2/* FormStructure.Chapter1.ch1DataProduction42 */),
_s4/* ch1DataProduction45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_s5/* ch1DataProduction44 */ = new T2(1,_s4/* FormStructure.Chapter1.ch1DataProduction45 */,_I/* GHC.Types.[] */),
_s6/* ch1DataProduction46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_s7/* ch1DataProduction43 */ = new T2(1,_s6/* FormStructure.Chapter1.ch1DataProduction46 */,_s5/* FormStructure.Chapter1.ch1DataProduction44 */),
_s8/* ch1DataProduction47 */ = new T1(1,_rU/* FormStructure.Chapter1.ch1DataProduction38 */),
_s9/* ch1DataProduction49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_sa/* ch1DataProduction48 */ = new T1(1,_s9/* FormStructure.Chapter1.ch1DataProduction49 */),
_sb/* ch1DataProduction30 */ = {_:0,a:_sa/* FormStructure.Chapter1.ch1DataProduction48 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_s8/* FormStructure.Chapter1.ch1DataProduction47 */,d:_s7/* FormStructure.Chapter1.ch1DataProduction43 */,e:_s3/* FormStructure.Chapter1.ch1DataProduction41 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_s1/* FormStructure.Chapter1.ch1DataProduction31 */},
_sc/* ch1DataProduction29 */ = new T2(3,_sb/* FormStructure.Chapter1.ch1DataProduction30 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_sd/* ch1DataProduction15 */ = new T2(1,_sc/* FormStructure.Chapter1.ch1DataProduction29 */,_rO/* FormStructure.Chapter1.ch1DataProduction16 */),
_se/* ch1DataProduction53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_sf/* ch1DataProduction52 */ = new T1(1,_se/* FormStructure.Chapter1.ch1DataProduction53 */),
_sg/* ch1DataProduction56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_sh/* ch1DataProduction55 */ = new T2(1,_sg/* FormStructure.Chapter1.ch1DataProduction56 */,_I/* GHC.Types.[] */),
_si/* ch1DataProduction54 */ = new T2(1,_s6/* FormStructure.Chapter1.ch1DataProduction46 */,_sh/* FormStructure.Chapter1.ch1DataProduction55 */),
_sj/* ch1DataProduction57 */ = new T1(1,_rW/* FormStructure.Chapter1.ch1DataProduction39 */),
_sk/* ch1DataProduction59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_sl/* ch1DataProduction58 */ = new T1(1,_sk/* FormStructure.Chapter1.ch1DataProduction59 */),
_sm/* ch1DataProduction51 */ = {_:0,a:_sl/* FormStructure.Chapter1.ch1DataProduction58 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_sj/* FormStructure.Chapter1.ch1DataProduction57 */,d:_si/* FormStructure.Chapter1.ch1DataProduction54 */,e:_sf/* FormStructure.Chapter1.ch1DataProduction52 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_s1/* FormStructure.Chapter1.ch1DataProduction31 */},
_sn/* ch1DataProduction50 */ = new T2(3,_sm/* FormStructure.Chapter1.ch1DataProduction51 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_so/* ch1DataProduction14 */ = new T2(1,_sn/* FormStructure.Chapter1.ch1DataProduction50 */,_sd/* FormStructure.Chapter1.ch1DataProduction15 */),
_sp/* ch1DataProduction63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_sq/* ch1DataProduction62 */ = new T2(1,_sp/* FormStructure.Chapter1.ch1DataProduction63 */,_I/* GHC.Types.[] */),
_sr/* ch1DataProduction64 */ = new T1(1,_rY/* FormStructure.Chapter1.ch1DataProduction40 */),
_ss/* ch1DataProduction66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_st/* ch1DataProduction65 */ = new T1(1,_ss/* FormStructure.Chapter1.ch1DataProduction66 */),
_su/* ch1DataProduction61 */ = {_:0,a:_st/* FormStructure.Chapter1.ch1DataProduction65 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_sr/* FormStructure.Chapter1.ch1DataProduction64 */,d:_sq/* FormStructure.Chapter1.ch1DataProduction62 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_s1/* FormStructure.Chapter1.ch1DataProduction31 */},
_sv/* ch1DataProduction60 */ = new T2(3,_su/* FormStructure.Chapter1.ch1DataProduction61 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_sw/* ch1DataProduction13 */ = new T2(1,_sv/* FormStructure.Chapter1.ch1DataProduction60 */,_so/* FormStructure.Chapter1.ch1DataProduction14 */),
_sx/* ch1DataProduction70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_sy/* ch1DataProduction69 */ = new T1(1,_sx/* FormStructure.Chapter1.ch1DataProduction70 */),
_sz/* ch1DataProduction68 */ = {_:0,a:_sy/* FormStructure.Chapter1.ch1DataProduction69 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_sA/* ch1DataProduction12 */ = new T3(7,_sz/* FormStructure.Chapter1.ch1DataProduction68 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_sw/* FormStructure.Chapter1.ch1DataProduction13 */),
_sB/* ch1DataProduction10 */ = new T2(1,_sA/* FormStructure.Chapter1.ch1DataProduction12 */,_rA/* FormStructure.Chapter1.ch1DataProduction11 */),
_sC/* ch1DataProduction112 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Skip if you do not want to share"));
}),
_sD/* ch1DataProduction111 */ = new T1(1,_sC/* FormStructure.Chapter1.ch1DataProduction112 */),
_sE/* ch1DataProduction114 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_sF/* ch1DataProduction113 */ = new T1(1,_sE/* FormStructure.Chapter1.ch1DataProduction114 */),
_sG/* ch1DataProduction110 */ = {_:0,a:_sF/* FormStructure.Chapter1.ch1DataProduction113 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_sD/* FormStructure.Chapter1.ch1DataProduction111 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_sH/* ch1DataProduction91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-institutional"));
}),
_sI/* ch1DataProduction107 */ = new T1(1,_sH/* FormStructure.Chapter1.ch1DataProduction91 */),
_sJ/* ch1DataProduction109 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_sK/* ch1DataProduction108 */ = new T1(1,_sJ/* FormStructure.Chapter1.ch1DataProduction109 */),
_sL/* ch1DataProduction80 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-sum"));
}),
_sM/* ch1DataProduction88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-worldwide"));
}),
_sN/* ch1DataProduction87 */ = new T2(1,_sM/* FormStructure.Chapter1.ch1DataProduction88 */,_I/* GHC.Types.[] */),
_sO/* ch1DataProduction89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-european"));
}),
_sP/* ch1DataProduction86 */ = new T2(1,_sO/* FormStructure.Chapter1.ch1DataProduction89 */,_sN/* FormStructure.Chapter1.ch1DataProduction87 */),
_sQ/* ch1DataProduction90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-national"));
}),
_sR/* ch1DataProduction85 */ = new T2(1,_sQ/* FormStructure.Chapter1.ch1DataProduction90 */,_sP/* FormStructure.Chapter1.ch1DataProduction86 */),
_sS/* ch1DataProduction84 */ = new T2(1,_sH/* FormStructure.Chapter1.ch1DataProduction91 */,_sR/* FormStructure.Chapter1.ch1DataProduction85 */),
_sT/* ch1DataProduction_fundingSumRule */ = new T2(0,_sS/* FormStructure.Chapter1.ch1DataProduction84 */,_sL/* FormStructure.Chapter1.ch1DataProduction80 */),
_sU/* ch1DataProduction83 */ = new T2(1,_sT/* FormStructure.Chapter1.ch1DataProduction_fundingSumRule */,_rT/* FormStructure.Chapter1.ch1DataProduction32 */),
_sV/* ch1DataProduction106 */ = {_:0,a:_sK/* FormStructure.Chapter1.ch1DataProduction108 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_sI/* FormStructure.Chapter1.ch1DataProduction107 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_sU/* FormStructure.Chapter1.ch1DataProduction83 */},
_sW/* ch1DataProduction105 */ = new T2(3,_sV/* FormStructure.Chapter1.ch1DataProduction106 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_sX/* ch1DataProduction102 */ = new T1(1,_sQ/* FormStructure.Chapter1.ch1DataProduction90 */),
_sY/* ch1DataProduction104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_sZ/* ch1DataProduction103 */ = new T1(1,_sY/* FormStructure.Chapter1.ch1DataProduction104 */),
_t0/* ch1DataProduction101 */ = {_:0,a:_sZ/* FormStructure.Chapter1.ch1DataProduction103 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_sX/* FormStructure.Chapter1.ch1DataProduction102 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_sU/* FormStructure.Chapter1.ch1DataProduction83 */},
_t1/* ch1DataProduction100 */ = new T2(3,_t0/* FormStructure.Chapter1.ch1DataProduction101 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_t2/* ch1DataProduction79 */ = new T1(1,_sL/* FormStructure.Chapter1.ch1DataProduction80 */),
_t3/* ch1DataProduction78 */ = {_:0,a:_rL/* FormStructure.Chapter1.ch1DataProduction27 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_t2/* FormStructure.Chapter1.ch1DataProduction79 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_rH/* FormStructure.Chapter1.ch1DataProduction21 */},
_t4/* ch1DataProduction77 */ = new T2(3,_t3/* FormStructure.Chapter1.ch1DataProduction78 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_t5/* ch1DataProduction76 */ = new T2(1,_t4/* FormStructure.Chapter1.ch1DataProduction77 */,_I/* GHC.Types.[] */),
_t6/* ch1DataProduction92 */ = new T1(1,_sM/* FormStructure.Chapter1.ch1DataProduction88 */),
_t7/* ch1DataProduction94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_t8/* ch1DataProduction93 */ = new T1(1,_t7/* FormStructure.Chapter1.ch1DataProduction94 */),
_t9/* ch1DataProduction82 */ = {_:0,a:_t8/* FormStructure.Chapter1.ch1DataProduction93 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_t6/* FormStructure.Chapter1.ch1DataProduction92 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_sU/* FormStructure.Chapter1.ch1DataProduction83 */},
_ta/* ch1DataProduction81 */ = new T2(3,_t9/* FormStructure.Chapter1.ch1DataProduction82 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_tb/* ch1DataProduction75 */ = new T2(1,_ta/* FormStructure.Chapter1.ch1DataProduction81 */,_t5/* FormStructure.Chapter1.ch1DataProduction76 */),
_tc/* ch1DataProduction97 */ = new T1(1,_sO/* FormStructure.Chapter1.ch1DataProduction89 */),
_td/* ch1DataProduction99 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_te/* ch1DataProduction98 */ = new T1(1,_td/* FormStructure.Chapter1.ch1DataProduction99 */),
_tf/* ch1DataProduction96 */ = {_:0,a:_te/* FormStructure.Chapter1.ch1DataProduction98 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_tc/* FormStructure.Chapter1.ch1DataProduction97 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_sU/* FormStructure.Chapter1.ch1DataProduction83 */},
_tg/* ch1DataProduction95 */ = new T2(3,_tf/* FormStructure.Chapter1.ch1DataProduction96 */,_rC/* FormStructure.Chapter1.ch1DataProduction18 */),
_th/* ch1DataProduction74 */ = new T2(1,_tg/* FormStructure.Chapter1.ch1DataProduction95 */,_tb/* FormStructure.Chapter1.ch1DataProduction75 */),
_ti/* ch1DataProduction73 */ = new T2(1,_t1/* FormStructure.Chapter1.ch1DataProduction100 */,_th/* FormStructure.Chapter1.ch1DataProduction74 */),
_tj/* ch1DataProduction72 */ = new T2(1,_sW/* FormStructure.Chapter1.ch1DataProduction105 */,_ti/* FormStructure.Chapter1.ch1DataProduction73 */),
_tk/* ch1DataProduction71 */ = new T3(7,_sG/* FormStructure.Chapter1.ch1DataProduction110 */,_r1/* FormStructure.Chapter1.ch1DataProduction67 */,_tj/* FormStructure.Chapter1.ch1DataProduction72 */),
_tl/* ch1DataProduction9 */ = new T2(1,_tk/* FormStructure.Chapter1.ch1DataProduction71 */,_sB/* FormStructure.Chapter1.ch1DataProduction10 */),
_tm/* ch1DataProduction8 */ = new T2(1,_rz/* FormStructure.Chapter1.ch1DataProduction115 */,_tl/* FormStructure.Chapter1.ch1DataProduction9 */),
_tn/* ch1DataProduction7 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_pz/* FormStructure.Chapter1.ch1DataProduction223 */,_tm/* FormStructure.Chapter1.ch1DataProduction8 */),
_to/* ch1DataProduction3 */ = new T2(1,_tn/* FormStructure.Chapter1.ch1DataProduction7 */,_py/* FormStructure.Chapter1.ch1DataProduction4 */),
_tp/* ch1DataProduction2 */ = new T2(4,_pv/* FormStructure.Chapter1.ch1DataProduction224 */,_to/* FormStructure.Chapter1.ch1DataProduction3 */),
_tq/* ch1DataProduction1 */ = new T2(1,_tp/* FormStructure.Chapter1.ch1DataProduction2 */,_I/* GHC.Types.[] */),
_tr/* ch1DataProduction229 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1.Production "));
}),
_ts/* ch1DataProduction228 */ = new T1(1,_tr/* FormStructure.Chapter1.ch1DataProduction229 */),
_tt/* ch1DataProduction227 */ = {_:0,a:_ts/* FormStructure.Chapter1.ch1DataProduction228 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tu/* ch1DataProduction */ = new T2(6,_tt/* FormStructure.Chapter1.ch1DataProduction227 */,_tq/* FormStructure.Chapter1.ch1DataProduction1 */),
_tv/* ch2DataProcessing256 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you process raw data, i.e. you produce secondary data?"));
}),
_tw/* ch2DataProcessing255 */ = new T1(1,_tv/* FormStructure.Chapter2.ch2DataProcessing256 */),
_tx/* ch2DataProcessing254 */ = {_:0,a:_tw/* FormStructure.Chapter2.ch2DataProcessing255 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_ty/* ch2DataProcessing6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_tz/* ch2DataProcessing5 */ = new T1(0,_ty/* FormStructure.Chapter2.ch2DataProcessing6 */),
_tA/* ch2DataProcessing4 */ = new T2(1,_tz/* FormStructure.Chapter2.ch2DataProcessing5 */,_I/* GHC.Types.[] */),
_tB/* ch2DataProcessing153 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_tC/* ch2DataProcessing152 */ = new T1(0,_tB/* FormStructure.Chapter2.ch2DataProcessing153 */),
_tD/* ch2DataProcessing156 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_tE/* ch2DataProcessing155 */ = new T1(1,_tD/* FormStructure.Chapter2.ch2DataProcessing156 */),
_tF/* ch2DataProcessing154 */ = {_:0,a:_tE/* FormStructure.Chapter2.ch2DataProcessing155 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tG/* ch2DataProcessing151 */ = new T2(3,_tF/* FormStructure.Chapter2.ch2DataProcessing154 */,_tC/* FormStructure.Chapter2.ch2DataProcessing152 */),
_tH/* ch2DataProcessing150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_tI/* ch2DataProcessing149 */ = new T1(1,_tH/* FormStructure.Chapter2.ch2DataProcessing150 */),
_tJ/* ch2DataProcessing148 */ = {_:0,a:_tI/* FormStructure.Chapter2.ch2DataProcessing149 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_tK/* ch2DataProcessing21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_tL/* ch2DataProcessing20 */ = new T1(0,_tK/* FormStructure.Chapter2.ch2DataProcessing21 */),
_tM/* ch2DataProcessing208 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-sum"));
}),
_tN/* ch2DataProcessing207 */ = new T1(1,_tM/* FormStructure.Chapter2.ch2DataProcessing208 */),
_tO/* ch2DataProcessing26 */ = function(_tP/* sdhs */){
  return (E(_tP/* sdhs */)==100) ? true : false;
},
_tQ/* ch2DataProcessing25 */ = new T1(4,_tO/* FormStructure.Chapter2.ch2DataProcessing26 */),
_tR/* ch2DataProcessing24 */ = new T2(1,_tQ/* FormStructure.Chapter2.ch2DataProcessing25 */,_I/* GHC.Types.[] */),
_tS/* ch2DataProcessing23 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_tR/* FormStructure.Chapter2.ch2DataProcessing24 */),
_tT/* ch2DataProcessing30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_tU/* ch2DataProcessing29 */ = new T1(1,_tT/* FormStructure.Chapter2.ch2DataProcessing30 */),
_tV/* ch2DataProcessing206 */ = {_:0,a:_tU/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_tN/* FormStructure.Chapter2.ch2DataProcessing207 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_tS/* FormStructure.Chapter2.ch2DataProcessing23 */},
_tW/* ch2DataProcessing205 */ = new T2(3,_tV/* FormStructure.Chapter2.ch2DataProcessing206 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_tX/* ch2DataProcessing204 */ = new T2(1,_tW/* FormStructure.Chapter2.ch2DataProcessing205 */,_I/* GHC.Types.[] */),
_tY/* ch2DataProcessing132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_tZ/* ch2DataProcessing131 */ = new T1(1,_tY/* FormStructure.Chapter2.ch2DataProcessing132 */),
_u0/* ch2DataProcessing36 */ = function(_u1/* sdhm */){
  var _u2/* sdhn */ = E(_u1/* sdhm */);
  return (_u2/* sdhn */<0) ? false : _u2/* sdhn */<=100;
},
_u3/* ch2DataProcessing35 */ = new T1(4,_u0/* FormStructure.Chapter2.ch2DataProcessing36 */),
_u4/* ch2DataProcessing34 */ = new T2(1,_u3/* FormStructure.Chapter2.ch2DataProcessing35 */,_I/* GHC.Types.[] */),
_u5/* ch2DataProcessing216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-worldwide"));
}),
_u6/* ch2DataProcessing215 */ = new T2(1,_u5/* FormStructure.Chapter2.ch2DataProcessing216 */,_I/* GHC.Types.[] */),
_u7/* ch2DataProcessing217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-european"));
}),
_u8/* ch2DataProcessing214 */ = new T2(1,_u7/* FormStructure.Chapter2.ch2DataProcessing217 */,_u6/* FormStructure.Chapter2.ch2DataProcessing215 */),
_u9/* ch2DataProcessing218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-national"));
}),
_ua/* ch2DataProcessing213 */ = new T2(1,_u9/* FormStructure.Chapter2.ch2DataProcessing218 */,_u8/* FormStructure.Chapter2.ch2DataProcessing214 */),
_ub/* ch2DataProcessing219 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-institutional"));
}),
_uc/* ch2DataProcessing212 */ = new T2(1,_ub/* FormStructure.Chapter2.ch2DataProcessing219 */,_ua/* FormStructure.Chapter2.ch2DataProcessing213 */),
_ud/* ch2DataProcessing_fundingSumRule1 */ = new T2(0,_uc/* FormStructure.Chapter2.ch2DataProcessing212 */,_tM/* FormStructure.Chapter2.ch2DataProcessing208 */),
_ue/* ch2DataProcessing211 */ = new T2(1,_ud/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule1 */,_u4/* FormStructure.Chapter2.ch2DataProcessing34 */),
_uf/* ch2DataProcessing220 */ = new T1(1,_u5/* FormStructure.Chapter2.ch2DataProcessing216 */),
_ug/* ch2DataProcessing210 */ = {_:0,a:_tZ/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_uf/* FormStructure.Chapter2.ch2DataProcessing220 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_ue/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uh/* ch2DataProcessing209 */ = new T2(3,_ug/* FormStructure.Chapter2.ch2DataProcessing210 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_ui/* ch2DataProcessing203 */ = new T2(1,_uh/* FormStructure.Chapter2.ch2DataProcessing209 */,_tX/* FormStructure.Chapter2.ch2DataProcessing204 */),
_uj/* ch2DataProcessing137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_uk/* ch2DataProcessing136 */ = new T1(1,_uj/* FormStructure.Chapter2.ch2DataProcessing137 */),
_ul/* ch2DataProcessing223 */ = new T1(1,_u7/* FormStructure.Chapter2.ch2DataProcessing217 */),
_um/* ch2DataProcessing222 */ = {_:0,a:_uk/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_ul/* FormStructure.Chapter2.ch2DataProcessing223 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_ue/* FormStructure.Chapter2.ch2DataProcessing211 */},
_un/* ch2DataProcessing221 */ = new T2(3,_um/* FormStructure.Chapter2.ch2DataProcessing222 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uo/* ch2DataProcessing202 */ = new T2(1,_un/* FormStructure.Chapter2.ch2DataProcessing221 */,_ui/* FormStructure.Chapter2.ch2DataProcessing203 */),
_up/* ch2DataProcessing142 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_uq/* ch2DataProcessing141 */ = new T1(1,_up/* FormStructure.Chapter2.ch2DataProcessing142 */),
_ur/* ch2DataProcessing226 */ = new T1(1,_u9/* FormStructure.Chapter2.ch2DataProcessing218 */),
_us/* ch2DataProcessing225 */ = {_:0,a:_uq/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_ur/* FormStructure.Chapter2.ch2DataProcessing226 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_ue/* FormStructure.Chapter2.ch2DataProcessing211 */},
_ut/* ch2DataProcessing224 */ = new T2(3,_us/* FormStructure.Chapter2.ch2DataProcessing225 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uu/* ch2DataProcessing201 */ = new T2(1,_ut/* FormStructure.Chapter2.ch2DataProcessing224 */,_uo/* FormStructure.Chapter2.ch2DataProcessing202 */),
_uv/* ch2DataProcessing147 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_uw/* ch2DataProcessing146 */ = new T1(1,_uv/* FormStructure.Chapter2.ch2DataProcessing147 */),
_ux/* ch2DataProcessing229 */ = new T1(1,_ub/* FormStructure.Chapter2.ch2DataProcessing219 */),
_uy/* ch2DataProcessing228 */ = {_:0,a:_uw/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_ux/* FormStructure.Chapter2.ch2DataProcessing229 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_ue/* FormStructure.Chapter2.ch2DataProcessing211 */},
_uz/* ch2DataProcessing227 */ = new T2(3,_uy/* FormStructure.Chapter2.ch2DataProcessing228 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_uA/* ch2DataProcessing200 */ = new T2(1,_uz/* FormStructure.Chapter2.ch2DataProcessing227 */,_uu/* FormStructure.Chapter2.ch2DataProcessing201 */),
_uB/* ch2DataProcessing69 */ = 0,
_uC/* ch2DataProcessing199 */ = new T3(7,_tJ/* FormStructure.Chapter2.ch2DataProcessing148 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_uA/* FormStructure.Chapter2.ch2DataProcessing200 */),
_uD/* ch2DataProcessing198 */ = new T2(1,_uC/* FormStructure.Chapter2.ch2DataProcessing199 */,_I/* GHC.Types.[] */),
_uE/* ch2DataProcessing197 */ = new T2(1,_tG/* FormStructure.Chapter2.ch2DataProcessing151 */,_uD/* FormStructure.Chapter2.ch2DataProcessing198 */),
_uF/* ch2DataProcessing232 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_uG/* ch2DataProcessing231 */ = new T1(1,_uF/* FormStructure.Chapter2.ch2DataProcessing232 */),
_uH/* ch2DataProcessing230 */ = {_:0,a:_uG/* FormStructure.Chapter2.ch2DataProcessing231 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_uI/* ch2DataProcessing196 */ = new T3(7,_uH/* FormStructure.Chapter2.ch2DataProcessing230 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_uE/* FormStructure.Chapter2.ch2DataProcessing197 */),
_uJ/* ch2DataProcessing195 */ = new T2(1,_uI/* FormStructure.Chapter2.ch2DataProcessing196 */,_I/* GHC.Types.[] */),
_uK/* ch2DataProcessing170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_uL/* ch2DataProcessing169 */ = new T2(1,_uK/* FormStructure.Chapter2.ch2DataProcessing170 */,_I/* GHC.Types.[] */),
_uM/* ch2DataProcessing171 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_uN/* ch2DataProcessing168 */ = new T2(1,_uM/* FormStructure.Chapter2.ch2DataProcessing171 */,_uL/* FormStructure.Chapter2.ch2DataProcessing169 */),
_uO/* ch2DataProcessing172 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_uP/* ch2DataProcessing167 */ = new T2(1,_uO/* FormStructure.Chapter2.ch2DataProcessing172 */,_uN/* FormStructure.Chapter2.ch2DataProcessing168 */),
_uQ/* ch2DataProcessing173 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_uR/* ch2DataProcessing166 */ = new T2(1,_uQ/* FormStructure.Chapter2.ch2DataProcessing173 */,_uP/* FormStructure.Chapter2.ch2DataProcessing167 */),
_uS/* ch2DataProcessing165 */ = new T1(1,_uR/* FormStructure.Chapter2.ch2DataProcessing166 */),
_uT/* ch2DataProcessing236 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_uU/* ch2DataProcessing235 */ = new T1(1,_uT/* FormStructure.Chapter2.ch2DataProcessing236 */),
_uV/* ch2DataProcessing238 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_2"));
}),
_uW/* ch2DataProcessing237 */ = new T2(1,_uV/* FormStructure.Chapter2.ch2DataProcessing238 */,_I/* GHC.Types.[] */),
_uX/* ch2DataProcessing240 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific raw data volume"));
}),
_uY/* ch2DataProcessing239 */ = new T1(1,_uX/* FormStructure.Chapter2.ch2DataProcessing240 */),
_uZ/* ch2DataProcessing234 */ = {_:0,a:_uY/* FormStructure.Chapter2.ch2DataProcessing239 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_uW/* FormStructure.Chapter2.ch2DataProcessing237 */,e:_uU/* FormStructure.Chapter2.ch2DataProcessing235 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_v0/* ch2DataProcessing233 */ = new T2(3,_uZ/* FormStructure.Chapter2.ch2DataProcessing234 */,_uS/* FormStructure.Chapter2.ch2DataProcessing165 */),
_v1/* ch2DataProcessing194 */ = new T2(1,_v0/* FormStructure.Chapter2.ch2DataProcessing233 */,_uJ/* FormStructure.Chapter2.ch2DataProcessing195 */),
_v2/* ch2DataProcessing242 */ = new T1(0,_uM/* FormStructure.Chapter2.ch2DataProcessing171 */),
_v3/* ch2DataProcessing244 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_v4/* ch2DataProcessing246 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_v5/* ch2DataProcessing245 */ = new T2(1,_v4/* FormStructure.Chapter2.ch2DataProcessing246 */,_I/* GHC.Types.[] */),
_v6/* ch2DataProcessing248 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_v7/* ch2DataProcessing247 */ = new T1(1,_v6/* FormStructure.Chapter2.ch2DataProcessing248 */),
_v8/* ch2DataProcessing250 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_v9/* ch2DataProcessing249 */ = new T1(1,_v8/* FormStructure.Chapter2.ch2DataProcessing250 */),
_va/* ch2DataProcessing243 */ = {_:0,a:_v9/* FormStructure.Chapter2.ch2DataProcessing249 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_v7/* FormStructure.Chapter2.ch2DataProcessing247 */,d:_v5/* FormStructure.Chapter2.ch2DataProcessing245 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_v3/* FormStructure.Chapter2.ch2DataProcessing244 */},
_vb/* ch2DataProcessing241 */ = new T2(3,_va/* FormStructure.Chapter2.ch2DataProcessing243 */,_v2/* FormStructure.Chapter2.ch2DataProcessing242 */),
_vc/* ch2DataProcessing193 */ = new T2(1,_vb/* FormStructure.Chapter2.ch2DataProcessing241 */,_v1/* FormStructure.Chapter2.ch2DataProcessing194 */),
_vd/* ch2DataProcessing253 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_ve/* ch2DataProcessing252 */ = new T1(1,_vd/* FormStructure.Chapter2.ch2DataProcessing253 */),
_vf/* ch2DataProcessing251 */ = {_:0,a:_ve/* FormStructure.Chapter2.ch2DataProcessing252 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_vg/* ch2DataProcessing192 */ = new T3(7,_vf/* FormStructure.Chapter2.ch2DataProcessing251 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_vc/* FormStructure.Chapter2.ch2DataProcessing193 */),
_vh/* ch2DataProcessing118 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-sum"));
}),
_vi/* ch2DataProcessing117 */ = new T1(1,_vh/* FormStructure.Chapter2.ch2DataProcessing118 */),
_vj/* ch2DataProcessing116 */ = {_:0,a:_tU/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vi/* FormStructure.Chapter2.ch2DataProcessing117 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_tS/* FormStructure.Chapter2.ch2DataProcessing23 */},
_vk/* ch2DataProcessing115 */ = new T2(3,_vj/* FormStructure.Chapter2.ch2DataProcessing116 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vl/* ch2DataProcessing114 */ = new T2(1,_vk/* FormStructure.Chapter2.ch2DataProcessing115 */,_I/* GHC.Types.[] */),
_vm/* ch2DataProcessing126 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-worldwide"));
}),
_vn/* ch2DataProcessing125 */ = new T2(1,_vm/* FormStructure.Chapter2.ch2DataProcessing126 */,_I/* GHC.Types.[] */),
_vo/* ch2DataProcessing127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-european"));
}),
_vp/* ch2DataProcessing124 */ = new T2(1,_vo/* FormStructure.Chapter2.ch2DataProcessing127 */,_vn/* FormStructure.Chapter2.ch2DataProcessing125 */),
_vq/* ch2DataProcessing128 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-national"));
}),
_vr/* ch2DataProcessing123 */ = new T2(1,_vq/* FormStructure.Chapter2.ch2DataProcessing128 */,_vp/* FormStructure.Chapter2.ch2DataProcessing124 */),
_vs/* ch2DataProcessing129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-institutional"));
}),
_vt/* ch2DataProcessing122 */ = new T2(1,_vs/* FormStructure.Chapter2.ch2DataProcessing129 */,_vr/* FormStructure.Chapter2.ch2DataProcessing123 */),
_vu/* ch2DataProcessing_fundingSumRule */ = new T2(0,_vt/* FormStructure.Chapter2.ch2DataProcessing122 */,_vh/* FormStructure.Chapter2.ch2DataProcessing118 */),
_vv/* ch2DataProcessing121 */ = new T2(1,_vu/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule */,_u4/* FormStructure.Chapter2.ch2DataProcessing34 */),
_vw/* ch2DataProcessing130 */ = new T1(1,_vm/* FormStructure.Chapter2.ch2DataProcessing126 */),
_vx/* ch2DataProcessing120 */ = {_:0,a:_tZ/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vw/* FormStructure.Chapter2.ch2DataProcessing130 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_vv/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vy/* ch2DataProcessing119 */ = new T2(3,_vx/* FormStructure.Chapter2.ch2DataProcessing120 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vz/* ch2DataProcessing113 */ = new T2(1,_vy/* FormStructure.Chapter2.ch2DataProcessing119 */,_vl/* FormStructure.Chapter2.ch2DataProcessing114 */),
_vA/* ch2DataProcessing135 */ = new T1(1,_vo/* FormStructure.Chapter2.ch2DataProcessing127 */),
_vB/* ch2DataProcessing134 */ = {_:0,a:_uk/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vA/* FormStructure.Chapter2.ch2DataProcessing135 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_vv/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vC/* ch2DataProcessing133 */ = new T2(3,_vB/* FormStructure.Chapter2.ch2DataProcessing134 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vD/* ch2DataProcessing112 */ = new T2(1,_vC/* FormStructure.Chapter2.ch2DataProcessing133 */,_vz/* FormStructure.Chapter2.ch2DataProcessing113 */),
_vE/* ch2DataProcessing140 */ = new T1(1,_vq/* FormStructure.Chapter2.ch2DataProcessing128 */),
_vF/* ch2DataProcessing139 */ = {_:0,a:_uq/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vE/* FormStructure.Chapter2.ch2DataProcessing140 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_vv/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vG/* ch2DataProcessing138 */ = new T2(3,_vF/* FormStructure.Chapter2.ch2DataProcessing139 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vH/* ch2DataProcessing111 */ = new T2(1,_vG/* FormStructure.Chapter2.ch2DataProcessing138 */,_vD/* FormStructure.Chapter2.ch2DataProcessing112 */),
_vI/* ch2DataProcessing145 */ = new T1(1,_vs/* FormStructure.Chapter2.ch2DataProcessing129 */),
_vJ/* ch2DataProcessing144 */ = {_:0,a:_uw/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vI/* FormStructure.Chapter2.ch2DataProcessing145 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_vv/* FormStructure.Chapter2.ch2DataProcessing121 */},
_vK/* ch2DataProcessing143 */ = new T2(3,_vJ/* FormStructure.Chapter2.ch2DataProcessing144 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_vL/* ch2DataProcessing110 */ = new T2(1,_vK/* FormStructure.Chapter2.ch2DataProcessing143 */,_vH/* FormStructure.Chapter2.ch2DataProcessing111 */),
_vM/* ch2DataProcessing109 */ = new T3(7,_tJ/* FormStructure.Chapter2.ch2DataProcessing148 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_vL/* FormStructure.Chapter2.ch2DataProcessing110 */),
_vN/* ch2DataProcessing108 */ = new T2(1,_vM/* FormStructure.Chapter2.ch2DataProcessing109 */,_I/* GHC.Types.[] */),
_vO/* ch2DataProcessing107 */ = new T2(1,_tG/* FormStructure.Chapter2.ch2DataProcessing151 */,_vN/* FormStructure.Chapter2.ch2DataProcessing108 */),
_vP/* ch2DataProcessing159 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_vQ/* ch2DataProcessing158 */ = new T1(1,_vP/* FormStructure.Chapter2.ch2DataProcessing159 */),
_vR/* ch2DataProcessing161 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of data processing"));
}),
_vS/* ch2DataProcessing160 */ = new T1(1,_vR/* FormStructure.Chapter2.ch2DataProcessing161 */),
_vT/* ch2DataProcessing157 */ = {_:0,a:_vS/* FormStructure.Chapter2.ch2DataProcessing160 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_vQ/* FormStructure.Chapter2.ch2DataProcessing158 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_vU/* ch2DataProcessing106 */ = new T3(7,_vT/* FormStructure.Chapter2.ch2DataProcessing157 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_vO/* FormStructure.Chapter2.ch2DataProcessing107 */),
_vV/* ch2DataProcessing13 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_vW/* ch2DataProcessing28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-sum"));
}),
_vX/* ch2DataProcessing27 */ = new T1(1,_vW/* FormStructure.Chapter2.ch2DataProcessing28 */),
_vY/* ch2DataProcessing22 */ = {_:0,a:_tU/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_vX/* FormStructure.Chapter2.ch2DataProcessing27 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_tS/* FormStructure.Chapter2.ch2DataProcessing23 */},
_vZ/* ch2DataProcessing19 */ = new T2(3,_vY/* FormStructure.Chapter2.ch2DataProcessing22 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_w0/* ch2DataProcessing18 */ = new T2(1,_vZ/* FormStructure.Chapter2.ch2DataProcessing19 */,_I/* GHC.Types.[] */),
_w1/* ch2DataProcessing40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-open"));
}),
_w2/* ch2DataProcessing39 */ = new T2(1,_w1/* FormStructure.Chapter2.ch2DataProcessing40 */,_I/* GHC.Types.[] */),
_w3/* ch2DataProcessing41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-closed"));
}),
_w4/* ch2DataProcessing38 */ = new T2(1,_w3/* FormStructure.Chapter2.ch2DataProcessing41 */,_w2/* FormStructure.Chapter2.ch2DataProcessing39 */),
_w5/* ch2DataProcessing42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-inside"));
}),
_w6/* ch2DataProcessing37 */ = new T2(1,_w5/* FormStructure.Chapter2.ch2DataProcessing42 */,_w4/* FormStructure.Chapter2.ch2DataProcessing38 */),
_w7/* ch2DataProcessing_accSumRule */ = new T2(0,_w6/* FormStructure.Chapter2.ch2DataProcessing37 */,_vW/* FormStructure.Chapter2.ch2DataProcessing28 */),
_w8/* ch2DataProcessing33 */ = new T2(1,_w7/* FormStructure.Chapter2.ch2DataProcessing_accSumRule */,_u4/* FormStructure.Chapter2.ch2DataProcessing34 */),
_w9/* ch2DataProcessing44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_wa/* ch2DataProcessing43 */ = new T1(1,_w9/* FormStructure.Chapter2.ch2DataProcessing44 */),
_wb/* ch2DataProcessing47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_wc/* ch2DataProcessing46 */ = new T2(1,_wb/* FormStructure.Chapter2.ch2DataProcessing47 */,_I/* GHC.Types.[] */),
_wd/* ch2DataProcessing48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_we/* ch2DataProcessing45 */ = new T2(1,_wd/* FormStructure.Chapter2.ch2DataProcessing48 */,_wc/* FormStructure.Chapter2.ch2DataProcessing46 */),
_wf/* ch2DataProcessing49 */ = new T1(1,_w1/* FormStructure.Chapter2.ch2DataProcessing40 */),
_wg/* ch2DataProcessing51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_wh/* ch2DataProcessing50 */ = new T1(1,_wg/* FormStructure.Chapter2.ch2DataProcessing51 */),
_wi/* ch2DataProcessing32 */ = {_:0,a:_wh/* FormStructure.Chapter2.ch2DataProcessing50 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_wf/* FormStructure.Chapter2.ch2DataProcessing49 */,d:_we/* FormStructure.Chapter2.ch2DataProcessing45 */,e:_wa/* FormStructure.Chapter2.ch2DataProcessing43 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_w8/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wj/* ch2DataProcessing31 */ = new T2(3,_wi/* FormStructure.Chapter2.ch2DataProcessing32 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wk/* ch2DataProcessing17 */ = new T2(1,_wj/* FormStructure.Chapter2.ch2DataProcessing31 */,_w0/* FormStructure.Chapter2.ch2DataProcessing18 */),
_wl/* ch2DataProcessing55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_wm/* ch2DataProcessing54 */ = new T1(1,_wl/* FormStructure.Chapter2.ch2DataProcessing55 */),
_wn/* ch2DataProcessing58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_wo/* ch2DataProcessing57 */ = new T2(1,_wn/* FormStructure.Chapter2.ch2DataProcessing58 */,_I/* GHC.Types.[] */),
_wp/* ch2DataProcessing56 */ = new T2(1,_wd/* FormStructure.Chapter2.ch2DataProcessing48 */,_wo/* FormStructure.Chapter2.ch2DataProcessing57 */),
_wq/* ch2DataProcessing59 */ = new T1(1,_w3/* FormStructure.Chapter2.ch2DataProcessing41 */),
_wr/* ch2DataProcessing61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_ws/* ch2DataProcessing60 */ = new T1(1,_wr/* FormStructure.Chapter2.ch2DataProcessing61 */),
_wt/* ch2DataProcessing53 */ = {_:0,a:_ws/* FormStructure.Chapter2.ch2DataProcessing60 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_wq/* FormStructure.Chapter2.ch2DataProcessing59 */,d:_wp/* FormStructure.Chapter2.ch2DataProcessing56 */,e:_wm/* FormStructure.Chapter2.ch2DataProcessing54 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_w8/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wu/* ch2DataProcessing52 */ = new T2(3,_wt/* FormStructure.Chapter2.ch2DataProcessing53 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wv/* ch2DataProcessing16 */ = new T2(1,_wu/* FormStructure.Chapter2.ch2DataProcessing52 */,_wk/* FormStructure.Chapter2.ch2DataProcessing17 */),
_ww/* ch2DataProcessing65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_wx/* ch2DataProcessing64 */ = new T2(1,_ww/* FormStructure.Chapter2.ch2DataProcessing65 */,_I/* GHC.Types.[] */),
_wy/* ch2DataProcessing66 */ = new T1(1,_w5/* FormStructure.Chapter2.ch2DataProcessing42 */),
_wz/* ch2DataProcessing68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_wA/* ch2DataProcessing67 */ = new T1(1,_wz/* FormStructure.Chapter2.ch2DataProcessing68 */),
_wB/* ch2DataProcessing63 */ = {_:0,a:_wA/* FormStructure.Chapter2.ch2DataProcessing67 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_wy/* FormStructure.Chapter2.ch2DataProcessing66 */,d:_wx/* FormStructure.Chapter2.ch2DataProcessing64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_w8/* FormStructure.Chapter2.ch2DataProcessing33 */},
_wC/* ch2DataProcessing62 */ = new T2(3,_wB/* FormStructure.Chapter2.ch2DataProcessing63 */,_tL/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wD/* ch2DataProcessing15 */ = new T2(1,_wC/* FormStructure.Chapter2.ch2DataProcessing62 */,_wv/* FormStructure.Chapter2.ch2DataProcessing16 */),
_wE/* ch2DataProcessing72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_wF/* ch2DataProcessing71 */ = new T1(1,_wE/* FormStructure.Chapter2.ch2DataProcessing72 */),
_wG/* ch2DataProcessing70 */ = {_:0,a:_wF/* FormStructure.Chapter2.ch2DataProcessing71 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_wH/* ch2DataProcessing14 */ = new T3(7,_wG/* FormStructure.Chapter2.ch2DataProcessing70 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_wD/* FormStructure.Chapter2.ch2DataProcessing15 */),
_wI/* ch2DataProcessing12 */ = new T2(1,_wH/* FormStructure.Chapter2.ch2DataProcessing14 */,_vV/* FormStructure.Chapter2.ch2DataProcessing13 */),
_wJ/* ch2DataProcessing103 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_wK/* ch2DataProcessing102 */ = new T1(1,_wJ/* FormStructure.Chapter2.ch2DataProcessing103 */),
_wL/* ch2DataProcessing105 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_wM/* ch2DataProcessing104 */ = new T1(1,_wL/* FormStructure.Chapter2.ch2DataProcessing105 */),
_wN/* ch2DataProcessing101 */ = {_:0,a:_wM/* FormStructure.Chapter2.ch2DataProcessing104 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_wK/* FormStructure.Chapter2.ch2DataProcessing102 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_wO/* ch2DataProcessing82 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_wP/* ch2DataProcessing81 */ = new T1(0,_wO/* FormStructure.Chapter2.ch2DataProcessing82 */),
_wQ/* ch2DataProcessing80 */ = new T2(1,_wP/* FormStructure.Chapter2.ch2DataProcessing81 */,_I/* GHC.Types.[] */),
_wR/* ch2DataProcessing84 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_wS/* ch2DataProcessing83 */ = new T1(0,_wR/* FormStructure.Chapter2.ch2DataProcessing84 */),
_wT/* ch2DataProcessing79 */ = new T2(1,_wS/* FormStructure.Chapter2.ch2DataProcessing83 */,_wQ/* FormStructure.Chapter2.ch2DataProcessing80 */),
_wU/* ch2DataProcessing86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_wV/* ch2DataProcessing85 */ = new T1(0,_wU/* FormStructure.Chapter2.ch2DataProcessing86 */),
_wW/* ch2DataProcessing78 */ = new T2(1,_wV/* FormStructure.Chapter2.ch2DataProcessing85 */,_wT/* FormStructure.Chapter2.ch2DataProcessing79 */),
_wX/* ch2DataProcessing88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_wY/* ch2DataProcessing87 */ = new T1(0,_wX/* FormStructure.Chapter2.ch2DataProcessing88 */),
_wZ/* ch2DataProcessing77 */ = new T2(1,_wY/* FormStructure.Chapter2.ch2DataProcessing87 */,_wW/* FormStructure.Chapter2.ch2DataProcessing78 */),
_x0/* ch2DataProcessing91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_x1/* ch2DataProcessing90 */ = new T1(1,_x0/* FormStructure.Chapter2.ch2DataProcessing91 */),
_x2/* ch2DataProcessing93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_x3/* ch2DataProcessing92 */ = new T1(1,_x2/* FormStructure.Chapter2.ch2DataProcessing93 */),
_x4/* ch2DataProcessing89 */ = {_:0,a:_x3/* FormStructure.Chapter2.ch2DataProcessing92 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_x1/* FormStructure.Chapter2.ch2DataProcessing90 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_x5/* ch2DataProcessing76 */ = new T2(4,_x4/* FormStructure.Chapter2.ch2DataProcessing89 */,_wZ/* FormStructure.Chapter2.ch2DataProcessing77 */),
_x6/* ch2DataProcessing75 */ = new T2(1,_x5/* FormStructure.Chapter2.ch2DataProcessing76 */,_I/* GHC.Types.[] */),
_x7/* ch2DataProcessing97 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_x8/* ch2DataProcessing96 */ = new T1(0,_x7/* FormStructure.Chapter2.ch2DataProcessing97 */),
_x9/* ch2DataProcessing95 */ = new T2(1,_x8/* FormStructure.Chapter2.ch2DataProcessing96 */,_tA/* FormStructure.Chapter2.ch2DataProcessing4 */),
_xa/* ch2DataProcessing100 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_xb/* ch2DataProcessing99 */ = new T1(1,_xa/* FormStructure.Chapter2.ch2DataProcessing100 */),
_xc/* ch2DataProcessing98 */ = {_:0,a:_xb/* FormStructure.Chapter2.ch2DataProcessing99 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xd/* ch2DataProcessing94 */ = new T2(4,_xc/* FormStructure.Chapter2.ch2DataProcessing98 */,_x9/* FormStructure.Chapter2.ch2DataProcessing95 */),
_xe/* ch2DataProcessing74 */ = new T2(1,_xd/* FormStructure.Chapter2.ch2DataProcessing94 */,_x6/* FormStructure.Chapter2.ch2DataProcessing75 */),
_xf/* ch2DataProcessing73 */ = new T3(7,_wN/* FormStructure.Chapter2.ch2DataProcessing101 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_xe/* FormStructure.Chapter2.ch2DataProcessing74 */),
_xg/* ch2DataProcessing11 */ = new T2(1,_xf/* FormStructure.Chapter2.ch2DataProcessing73 */,_wI/* FormStructure.Chapter2.ch2DataProcessing12 */),
_xh/* ch2DataProcessing10 */ = new T2(1,_vU/* FormStructure.Chapter2.ch2DataProcessing106 */,_xg/* FormStructure.Chapter2.ch2DataProcessing11 */),
_xi/* ch2DataProcessing176 */ = new T2(1,_pY/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_xj/* ch2DataProcessing178 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_xk/* ch2DataProcessing179 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_xl/* ch2DataProcessing177 */ = new T2(2,_xk/* FormStructure.Chapter2.ch2DataProcessing179 */,_xj/* FormStructure.Chapter2.ch2DataProcessing178 */),
_xm/* ch2DataProcessing175 */ = new T2(1,_xl/* FormStructure.Chapter2.ch2DataProcessing177 */,_xi/* FormStructure.Chapter2.ch2DataProcessing176 */),
_xn/* ch2DataProcessing181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_xo/* ch2DataProcessing180 */ = new T1(1,_xn/* FormStructure.Chapter2.ch2DataProcessing181 */),
_xp/* ch2DataProcessing184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_xq/* ch2DataProcessing183 */ = new T2(1,_xp/* FormStructure.Chapter2.ch2DataProcessing184 */,_I/* GHC.Types.[] */),
_xr/* ch2DataProcessing185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_xs/* ch2DataProcessing182 */ = new T2(1,_xr/* FormStructure.Chapter2.ch2DataProcessing185 */,_xq/* FormStructure.Chapter2.ch2DataProcessing183 */),
_xt/* ch2DataProcessing186 */ = new T1(1,_xk/* FormStructure.Chapter2.ch2DataProcessing179 */),
_xu/* ch2DataProcessing188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_xv/* ch2DataProcessing187 */ = new T1(1,_xu/* FormStructure.Chapter2.ch2DataProcessing188 */),
_xw/* ch2DataProcessing174 */ = {_:0,a:_xv/* FormStructure.Chapter2.ch2DataProcessing187 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_xt/* FormStructure.Chapter2.ch2DataProcessing186 */,d:_xs/* FormStructure.Chapter2.ch2DataProcessing182 */,e:_xo/* FormStructure.Chapter2.ch2DataProcessing180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_xm/* FormStructure.Chapter2.ch2DataProcessing175 */},
_xx/* ch2DataProcessing164 */ = new T2(3,_xw/* FormStructure.Chapter2.ch2DataProcessing174 */,_uS/* FormStructure.Chapter2.ch2DataProcessing165 */),
_xy/* ch2DataProcessing163 */ = new T2(1,_xx/* FormStructure.Chapter2.ch2DataProcessing164 */,_I/* GHC.Types.[] */),
_xz/* ch2DataProcessing191 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_xA/* ch2DataProcessing190 */ = new T1(1,_xz/* FormStructure.Chapter2.ch2DataProcessing191 */),
_xB/* ch2DataProcessing189 */ = {_:0,a:_xA/* FormStructure.Chapter2.ch2DataProcessing190 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xC/* ch2DataProcessing162 */ = new T3(7,_xB/* FormStructure.Chapter2.ch2DataProcessing189 */,_uB/* FormStructure.Chapter2.ch2DataProcessing69 */,_xy/* FormStructure.Chapter2.ch2DataProcessing163 */),
_xD/* ch2DataProcessing9 */ = new T2(1,_xC/* FormStructure.Chapter2.ch2DataProcessing162 */,_xh/* FormStructure.Chapter2.ch2DataProcessing10 */),
_xE/* ch2DataProcessing8 */ = new T2(1,_vg/* FormStructure.Chapter2.ch2DataProcessing192 */,_xD/* FormStructure.Chapter2.ch2DataProcessing9 */),
_xF/* ch2DataProcessing7 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_x7/* FormStructure.Chapter2.ch2DataProcessing97 */,_xE/* FormStructure.Chapter2.ch2DataProcessing8 */),
_xG/* ch2DataProcessing3 */ = new T2(1,_xF/* FormStructure.Chapter2.ch2DataProcessing7 */,_tA/* FormStructure.Chapter2.ch2DataProcessing4 */),
_xH/* ch2DataProcessing2 */ = new T2(4,_tx/* FormStructure.Chapter2.ch2DataProcessing254 */,_xG/* FormStructure.Chapter2.ch2DataProcessing3 */),
_xI/* ch2DataProcessing1 */ = new T2(1,_xH/* FormStructure.Chapter2.ch2DataProcessing2 */,_I/* GHC.Types.[] */),
_xJ/* ch2DataProcessing259 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("2.Processing "));
}),
_xK/* ch2DataProcessing258 */ = new T1(1,_xJ/* FormStructure.Chapter2.ch2DataProcessing259 */),
_xL/* ch2DataProcessing257 */ = {_:0,a:_xK/* FormStructure.Chapter2.ch2DataProcessing258 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_xM/* ch2DataProcessing */ = new T2(6,_xL/* FormStructure.Chapter2.ch2DataProcessing257 */,_xI/* FormStructure.Chapter2.ch2DataProcessing1 */),
_xN/* ch3DataUsage264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you use data, i.e. to perform analyses?"));
}),
_xO/* ch3DataUsage263 */ = new T1(1,_xN/* FormStructure.Chapter3.ch3DataUsage264 */),
_xP/* ch3DataUsage262 */ = {_:0,a:_xO/* FormStructure.Chapter3.ch3DataUsage263 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xQ/* ch3DataUsage6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_xR/* ch3DataUsage5 */ = new T1(0,_xQ/* FormStructure.Chapter3.ch3DataUsage6 */),
_xS/* ch3DataUsage4 */ = new T2(1,_xR/* FormStructure.Chapter3.ch3DataUsage5 */,_I/* GHC.Types.[] */),
_xT/* ch3DataUsage258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("A typical usage is performing a certain analysis."));
}),
_xU/* ch3DataUsage257 */ = new T1(1,_xT/* FormStructure.Chapter3.ch3DataUsage258 */),
_xV/* ch3DataUsage260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Describe the usage"));
}),
_xW/* ch3DataUsage259 */ = new T1(1,_xV/* FormStructure.Chapter3.ch3DataUsage260 */),
_xX/* ch3DataUsage256 */ = {_:0,a:_xW/* FormStructure.Chapter3.ch3DataUsage259 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_xU/* FormStructure.Chapter3.ch3DataUsage257 */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_xY/* ch3DataUsage255 */ = new T1(1,_xX/* FormStructure.Chapter3.ch3DataUsage256 */),
_xZ/* ch3DataUsage254 */ = new T2(1,_xY/* FormStructure.Chapter3.ch3DataUsage255 */,_I/* GHC.Types.[] */),
_y0/* ch3DataUsage261 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_y1/* ch3DataUsage70 */ = 0,
_y2/* ch3DataUsage253 */ = new T3(7,_y0/* FormStructure.Chapter3.ch3DataUsage261 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_xZ/* FormStructure.Chapter3.ch3DataUsage254 */),
_y3/* ch3DataUsage119 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-sum"));
}),
_y4/* ch3DataUsage118 */ = new T1(1,_y3/* FormStructure.Chapter3.ch3DataUsage119 */),
_y5/* ch3DataUsage27 */ = function(_y6/* sema */){
  return (E(_y6/* sema */)==100) ? true : false;
},
_y7/* ch3DataUsage26 */ = new T1(4,_y5/* FormStructure.Chapter3.ch3DataUsage27 */),
_y8/* ch3DataUsage25 */ = new T2(1,_y7/* FormStructure.Chapter3.ch3DataUsage26 */,_I/* GHC.Types.[] */),
_y9/* ch3DataUsage24 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_y8/* FormStructure.Chapter3.ch3DataUsage25 */),
_ya/* ch3DataUsage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_yb/* ch3DataUsage30 */ = new T1(1,_ya/* FormStructure.Chapter3.ch3DataUsage31 */),
_yc/* ch3DataUsage117 */ = {_:0,a:_yb/* FormStructure.Chapter3.ch3DataUsage30 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_y4/* FormStructure.Chapter3.ch3DataUsage118 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_y9/* FormStructure.Chapter3.ch3DataUsage24 */},
_yd/* ch3DataUsage22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_ye/* ch3DataUsage21 */ = new T1(0,_yd/* FormStructure.Chapter3.ch3DataUsage22 */),
_yf/* ch3DataUsage116 */ = new T2(3,_yc/* FormStructure.Chapter3.ch3DataUsage117 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_yg/* ch3DataUsage115 */ = new T2(1,_yf/* FormStructure.Chapter3.ch3DataUsage116 */,_I/* GHC.Types.[] */),
_yh/* ch3DataUsage125 */ = function(_yi/* sem4 */){
  var _yj/* sem5 */ = E(_yi/* sem4 */);
  return (_yj/* sem5 */<0) ? false : _yj/* sem5 */<=100;
},
_yk/* ch3DataUsage124 */ = new T1(4,_yh/* FormStructure.Chapter3.ch3DataUsage125 */),
_yl/* ch3DataUsage123 */ = new T2(1,_yk/* FormStructure.Chapter3.ch3DataUsage124 */,_I/* GHC.Types.[] */),
_ym/* ch3DataUsage130 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-worldwide"));
}),
_yn/* ch3DataUsage129 */ = new T2(1,_ym/* FormStructure.Chapter3.ch3DataUsage130 */,_I/* GHC.Types.[] */),
_yo/* ch3DataUsage131 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-european"));
}),
_yp/* ch3DataUsage128 */ = new T2(1,_yo/* FormStructure.Chapter3.ch3DataUsage131 */,_yn/* FormStructure.Chapter3.ch3DataUsage129 */),
_yq/* ch3DataUsage132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-national"));
}),
_yr/* ch3DataUsage127 */ = new T2(1,_yq/* FormStructure.Chapter3.ch3DataUsage132 */,_yp/* FormStructure.Chapter3.ch3DataUsage128 */),
_ys/* ch3DataUsage133 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-institutional"));
}),
_yt/* ch3DataUsage126 */ = new T2(1,_ys/* FormStructure.Chapter3.ch3DataUsage133 */,_yr/* FormStructure.Chapter3.ch3DataUsage127 */),
_yu/* ch3DataUsage_fundingSumRule */ = new T2(0,_yt/* FormStructure.Chapter3.ch3DataUsage126 */,_y3/* FormStructure.Chapter3.ch3DataUsage119 */),
_yv/* ch3DataUsage122 */ = new T2(1,_yu/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule */,_yl/* FormStructure.Chapter3.ch3DataUsage123 */),
_yw/* ch3DataUsage134 */ = new T1(1,_ym/* FormStructure.Chapter3.ch3DataUsage130 */),
_yx/* ch3DataUsage136 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_yy/* ch3DataUsage135 */ = new T1(1,_yx/* FormStructure.Chapter3.ch3DataUsage136 */),
_yz/* ch3DataUsage121 */ = {_:0,a:_yy/* FormStructure.Chapter3.ch3DataUsage135 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_yw/* FormStructure.Chapter3.ch3DataUsage134 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_yv/* FormStructure.Chapter3.ch3DataUsage122 */},
_yA/* ch3DataUsage120 */ = new T2(3,_yz/* FormStructure.Chapter3.ch3DataUsage121 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_yB/* ch3DataUsage114 */ = new T2(1,_yA/* FormStructure.Chapter3.ch3DataUsage120 */,_yg/* FormStructure.Chapter3.ch3DataUsage115 */),
_yC/* ch3DataUsage139 */ = new T1(1,_yo/* FormStructure.Chapter3.ch3DataUsage131 */),
_yD/* ch3DataUsage141 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_yE/* ch3DataUsage140 */ = new T1(1,_yD/* FormStructure.Chapter3.ch3DataUsage141 */),
_yF/* ch3DataUsage138 */ = {_:0,a:_yE/* FormStructure.Chapter3.ch3DataUsage140 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_yC/* FormStructure.Chapter3.ch3DataUsage139 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_yv/* FormStructure.Chapter3.ch3DataUsage122 */},
_yG/* ch3DataUsage137 */ = new T2(3,_yF/* FormStructure.Chapter3.ch3DataUsage138 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_yH/* ch3DataUsage113 */ = new T2(1,_yG/* FormStructure.Chapter3.ch3DataUsage137 */,_yB/* FormStructure.Chapter3.ch3DataUsage114 */),
_yI/* ch3DataUsage144 */ = new T1(1,_yq/* FormStructure.Chapter3.ch3DataUsage132 */),
_yJ/* ch3DataUsage146 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_yK/* ch3DataUsage145 */ = new T1(1,_yJ/* FormStructure.Chapter3.ch3DataUsage146 */),
_yL/* ch3DataUsage143 */ = {_:0,a:_yK/* FormStructure.Chapter3.ch3DataUsage145 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_yI/* FormStructure.Chapter3.ch3DataUsage144 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_yv/* FormStructure.Chapter3.ch3DataUsage122 */},
_yM/* ch3DataUsage142 */ = new T2(3,_yL/* FormStructure.Chapter3.ch3DataUsage143 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_yN/* ch3DataUsage112 */ = new T2(1,_yM/* FormStructure.Chapter3.ch3DataUsage142 */,_yH/* FormStructure.Chapter3.ch3DataUsage113 */),
_yO/* ch3DataUsage149 */ = new T1(1,_ys/* FormStructure.Chapter3.ch3DataUsage133 */),
_yP/* ch3DataUsage151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_yQ/* ch3DataUsage150 */ = new T1(1,_yP/* FormStructure.Chapter3.ch3DataUsage151 */),
_yR/* ch3DataUsage148 */ = {_:0,a:_yQ/* FormStructure.Chapter3.ch3DataUsage150 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_yO/* FormStructure.Chapter3.ch3DataUsage149 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_yv/* FormStructure.Chapter3.ch3DataUsage122 */},
_yS/* ch3DataUsage147 */ = new T2(3,_yR/* FormStructure.Chapter3.ch3DataUsage148 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_yT/* ch3DataUsage111 */ = new T2(1,_yS/* FormStructure.Chapter3.ch3DataUsage147 */,_yN/* FormStructure.Chapter3.ch3DataUsage112 */),
_yU/* ch3DataUsage154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_yV/* ch3DataUsage153 */ = new T1(1,_yU/* FormStructure.Chapter3.ch3DataUsage154 */),
_yW/* ch3DataUsage152 */ = {_:0,a:_yV/* FormStructure.Chapter3.ch3DataUsage153 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_yX/* ch3DataUsage110 */ = new T3(7,_yW/* FormStructure.Chapter3.ch3DataUsage152 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_yT/* FormStructure.Chapter3.ch3DataUsage111 */),
_yY/* ch3DataUsage109 */ = new T2(1,_yX/* FormStructure.Chapter3.ch3DataUsage110 */,_I/* GHC.Types.[] */),
_yZ/* ch3DataUsage157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_z0/* ch3DataUsage156 */ = new T1(0,_yZ/* FormStructure.Chapter3.ch3DataUsage157 */),
_z1/* ch3DataUsage160 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_z2/* ch3DataUsage159 */ = new T1(1,_z1/* FormStructure.Chapter3.ch3DataUsage160 */),
_z3/* ch3DataUsage158 */ = {_:0,a:_z2/* FormStructure.Chapter3.ch3DataUsage159 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_z4/* ch3DataUsage155 */ = new T2(3,_z3/* FormStructure.Chapter3.ch3DataUsage158 */,_z0/* FormStructure.Chapter3.ch3DataUsage156 */),
_z5/* ch3DataUsage108 */ = new T2(1,_z4/* FormStructure.Chapter3.ch3DataUsage155 */,_yY/* FormStructure.Chapter3.ch3DataUsage109 */),
_z6/* ch3DataUsage163 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_z7/* ch3DataUsage162 */ = new T1(1,_z6/* FormStructure.Chapter3.ch3DataUsage163 */),
_z8/* ch3DataUsage165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of secondary data production"));
}),
_z9/* ch3DataUsage164 */ = new T1(1,_z8/* FormStructure.Chapter3.ch3DataUsage165 */),
_za/* ch3DataUsage161 */ = {_:0,a:_z9/* FormStructure.Chapter3.ch3DataUsage164 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_z7/* FormStructure.Chapter3.ch3DataUsage162 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_zb/* ch3DataUsage107 */ = new T3(7,_za/* FormStructure.Chapter3.ch3DataUsage161 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_z5/* FormStructure.Chapter3.ch3DataUsage108 */),
_zc/* ch3DataUsage14 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_zd/* ch3DataUsage29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-sum"));
}),
_ze/* ch3DataUsage28 */ = new T1(1,_zd/* FormStructure.Chapter3.ch3DataUsage29 */),
_zf/* ch3DataUsage23 */ = {_:0,a:_yb/* FormStructure.Chapter3.ch3DataUsage30 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_ze/* FormStructure.Chapter3.ch3DataUsage28 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_y9/* FormStructure.Chapter3.ch3DataUsage24 */},
_zg/* ch3DataUsage20 */ = new T2(3,_zf/* FormStructure.Chapter3.ch3DataUsage23 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_zh/* ch3DataUsage19 */ = new T2(1,_zg/* FormStructure.Chapter3.ch3DataUsage20 */,_I/* GHC.Types.[] */),
_zi/* ch3DataUsage37 */ = function(_zj/* seme */){
  return E(_zj/* seme */)<=100;
},
_zk/* ch3DataUsage36 */ = new T1(4,_zi/* FormStructure.Chapter3.ch3DataUsage37 */),
_zl/* ch3DataUsage35 */ = new T2(1,_zk/* FormStructure.Chapter3.ch3DataUsage36 */,_I/* GHC.Types.[] */),
_zm/* ch3DataUsage41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-open"));
}),
_zn/* ch3DataUsage40 */ = new T2(1,_zm/* FormStructure.Chapter3.ch3DataUsage41 */,_I/* GHC.Types.[] */),
_zo/* ch3DataUsage42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-closed"));
}),
_zp/* ch3DataUsage39 */ = new T2(1,_zo/* FormStructure.Chapter3.ch3DataUsage42 */,_zn/* FormStructure.Chapter3.ch3DataUsage40 */),
_zq/* ch3DataUsage43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-inside"));
}),
_zr/* ch3DataUsage38 */ = new T2(1,_zq/* FormStructure.Chapter3.ch3DataUsage43 */,_zp/* FormStructure.Chapter3.ch3DataUsage39 */),
_zs/* ch3DataUsage_accSumRule */ = new T2(0,_zr/* FormStructure.Chapter3.ch3DataUsage38 */,_zd/* FormStructure.Chapter3.ch3DataUsage29 */),
_zt/* ch3DataUsage34 */ = new T2(1,_zs/* FormStructure.Chapter3.ch3DataUsage_accSumRule */,_zl/* FormStructure.Chapter3.ch3DataUsage35 */),
_zu/* ch3DataUsage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_zv/* ch3DataUsage44 */ = new T1(1,_zu/* FormStructure.Chapter3.ch3DataUsage45 */),
_zw/* ch3DataUsage48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_zx/* ch3DataUsage47 */ = new T2(1,_zw/* FormStructure.Chapter3.ch3DataUsage48 */,_I/* GHC.Types.[] */),
_zy/* ch3DataUsage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_zz/* ch3DataUsage46 */ = new T2(1,_zy/* FormStructure.Chapter3.ch3DataUsage49 */,_zx/* FormStructure.Chapter3.ch3DataUsage47 */),
_zA/* ch3DataUsage50 */ = new T1(1,_zm/* FormStructure.Chapter3.ch3DataUsage41 */),
_zB/* ch3DataUsage52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_zC/* ch3DataUsage51 */ = new T1(1,_zB/* FormStructure.Chapter3.ch3DataUsage52 */),
_zD/* ch3DataUsage33 */ = {_:0,a:_zC/* FormStructure.Chapter3.ch3DataUsage51 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_zA/* FormStructure.Chapter3.ch3DataUsage50 */,d:_zz/* FormStructure.Chapter3.ch3DataUsage46 */,e:_zv/* FormStructure.Chapter3.ch3DataUsage44 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_zt/* FormStructure.Chapter3.ch3DataUsage34 */},
_zE/* ch3DataUsage32 */ = new T2(3,_zD/* FormStructure.Chapter3.ch3DataUsage33 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_zF/* ch3DataUsage18 */ = new T2(1,_zE/* FormStructure.Chapter3.ch3DataUsage32 */,_zh/* FormStructure.Chapter3.ch3DataUsage19 */),
_zG/* ch3DataUsage56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_zH/* ch3DataUsage55 */ = new T1(1,_zG/* FormStructure.Chapter3.ch3DataUsage56 */),
_zI/* ch3DataUsage59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_zJ/* ch3DataUsage58 */ = new T2(1,_zI/* FormStructure.Chapter3.ch3DataUsage59 */,_I/* GHC.Types.[] */),
_zK/* ch3DataUsage57 */ = new T2(1,_zy/* FormStructure.Chapter3.ch3DataUsage49 */,_zJ/* FormStructure.Chapter3.ch3DataUsage58 */),
_zL/* ch3DataUsage60 */ = new T1(1,_zo/* FormStructure.Chapter3.ch3DataUsage42 */),
_zM/* ch3DataUsage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_zN/* ch3DataUsage61 */ = new T1(1,_zM/* FormStructure.Chapter3.ch3DataUsage62 */),
_zO/* ch3DataUsage54 */ = {_:0,a:_zN/* FormStructure.Chapter3.ch3DataUsage61 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_zL/* FormStructure.Chapter3.ch3DataUsage60 */,d:_zK/* FormStructure.Chapter3.ch3DataUsage57 */,e:_zH/* FormStructure.Chapter3.ch3DataUsage55 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_zt/* FormStructure.Chapter3.ch3DataUsage34 */},
_zP/* ch3DataUsage53 */ = new T2(3,_zO/* FormStructure.Chapter3.ch3DataUsage54 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_zQ/* ch3DataUsage17 */ = new T2(1,_zP/* FormStructure.Chapter3.ch3DataUsage53 */,_zF/* FormStructure.Chapter3.ch3DataUsage18 */),
_zR/* ch3DataUsage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_zS/* ch3DataUsage65 */ = new T2(1,_zR/* FormStructure.Chapter3.ch3DataUsage66 */,_I/* GHC.Types.[] */),
_zT/* ch3DataUsage67 */ = new T1(1,_zq/* FormStructure.Chapter3.ch3DataUsage43 */),
_zU/* ch3DataUsage69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_zV/* ch3DataUsage68 */ = new T1(1,_zU/* FormStructure.Chapter3.ch3DataUsage69 */),
_zW/* ch3DataUsage64 */ = {_:0,a:_zV/* FormStructure.Chapter3.ch3DataUsage68 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_zT/* FormStructure.Chapter3.ch3DataUsage67 */,d:_zS/* FormStructure.Chapter3.ch3DataUsage65 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_zt/* FormStructure.Chapter3.ch3DataUsage34 */},
_zX/* ch3DataUsage63 */ = new T2(3,_zW/* FormStructure.Chapter3.ch3DataUsage64 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_zY/* ch3DataUsage16 */ = new T2(1,_zX/* FormStructure.Chapter3.ch3DataUsage63 */,_zQ/* FormStructure.Chapter3.ch3DataUsage17 */),
_zZ/* ch3DataUsage73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_A0/* ch3DataUsage72 */ = new T1(1,_zZ/* FormStructure.Chapter3.ch3DataUsage73 */),
_A1/* ch3DataUsage71 */ = {_:0,a:_A0/* FormStructure.Chapter3.ch3DataUsage72 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_A2/* ch3DataUsage15 */ = new T3(7,_A1/* FormStructure.Chapter3.ch3DataUsage71 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_zY/* FormStructure.Chapter3.ch3DataUsage16 */),
_A3/* ch3DataUsage13 */ = new T2(1,_A2/* FormStructure.Chapter3.ch3DataUsage15 */,_zc/* FormStructure.Chapter3.ch3DataUsage14 */),
_A4/* ch3DataUsage104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_A5/* ch3DataUsage103 */ = new T1(1,_A4/* FormStructure.Chapter3.ch3DataUsage104 */),
_A6/* ch3DataUsage106 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_A7/* ch3DataUsage105 */ = new T1(1,_A6/* FormStructure.Chapter3.ch3DataUsage106 */),
_A8/* ch3DataUsage102 */ = {_:0,a:_A7/* FormStructure.Chapter3.ch3DataUsage105 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_A5/* FormStructure.Chapter3.ch3DataUsage103 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_A9/* ch3DataUsage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_Aa/* ch3DataUsage82 */ = new T1(0,_A9/* FormStructure.Chapter3.ch3DataUsage83 */),
_Ab/* ch3DataUsage81 */ = new T2(1,_Aa/* FormStructure.Chapter3.ch3DataUsage82 */,_I/* GHC.Types.[] */),
_Ac/* ch3DataUsage85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_Ad/* ch3DataUsage84 */ = new T1(0,_Ac/* FormStructure.Chapter3.ch3DataUsage85 */),
_Ae/* ch3DataUsage80 */ = new T2(1,_Ad/* FormStructure.Chapter3.ch3DataUsage84 */,_Ab/* FormStructure.Chapter3.ch3DataUsage81 */),
_Af/* ch3DataUsage87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_Ag/* ch3DataUsage86 */ = new T1(0,_Af/* FormStructure.Chapter3.ch3DataUsage87 */),
_Ah/* ch3DataUsage79 */ = new T2(1,_Ag/* FormStructure.Chapter3.ch3DataUsage86 */,_Ae/* FormStructure.Chapter3.ch3DataUsage80 */),
_Ai/* ch3DataUsage89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_Aj/* ch3DataUsage88 */ = new T1(0,_Ai/* FormStructure.Chapter3.ch3DataUsage89 */),
_Ak/* ch3DataUsage78 */ = new T2(1,_Aj/* FormStructure.Chapter3.ch3DataUsage88 */,_Ah/* FormStructure.Chapter3.ch3DataUsage79 */),
_Al/* ch3DataUsage92 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_Am/* ch3DataUsage91 */ = new T1(1,_Al/* FormStructure.Chapter3.ch3DataUsage92 */),
_An/* ch3DataUsage94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_Ao/* ch3DataUsage93 */ = new T1(1,_An/* FormStructure.Chapter3.ch3DataUsage94 */),
_Ap/* ch3DataUsage90 */ = {_:0,a:_Ao/* FormStructure.Chapter3.ch3DataUsage93 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Am/* FormStructure.Chapter3.ch3DataUsage91 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Aq/* ch3DataUsage77 */ = new T2(4,_Ap/* FormStructure.Chapter3.ch3DataUsage90 */,_Ak/* FormStructure.Chapter3.ch3DataUsage78 */),
_Ar/* ch3DataUsage76 */ = new T2(1,_Aq/* FormStructure.Chapter3.ch3DataUsage77 */,_I/* GHC.Types.[] */),
_As/* ch3DataUsage98 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_At/* ch3DataUsage97 */ = new T1(0,_As/* FormStructure.Chapter3.ch3DataUsage98 */),
_Au/* ch3DataUsage96 */ = new T2(1,_At/* FormStructure.Chapter3.ch3DataUsage97 */,_xS/* FormStructure.Chapter3.ch3DataUsage4 */),
_Av/* ch3DataUsage101 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_Aw/* ch3DataUsage100 */ = new T1(1,_Av/* FormStructure.Chapter3.ch3DataUsage101 */),
_Ax/* ch3DataUsage99 */ = {_:0,a:_Aw/* FormStructure.Chapter3.ch3DataUsage100 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ay/* ch3DataUsage95 */ = new T2(4,_Ax/* FormStructure.Chapter3.ch3DataUsage99 */,_Au/* FormStructure.Chapter3.ch3DataUsage96 */),
_Az/* ch3DataUsage75 */ = new T2(1,_Ay/* FormStructure.Chapter3.ch3DataUsage95 */,_Ar/* FormStructure.Chapter3.ch3DataUsage76 */),
_AA/* ch3DataUsage74 */ = new T3(7,_A8/* FormStructure.Chapter3.ch3DataUsage102 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_Az/* FormStructure.Chapter3.ch3DataUsage75 */),
_AB/* ch3DataUsage12 */ = new T2(1,_AA/* FormStructure.Chapter3.ch3DataUsage74 */,_A3/* FormStructure.Chapter3.ch3DataUsage13 */),
_AC/* ch3DataUsage11 */ = new T2(1,_zb/* FormStructure.Chapter3.ch3DataUsage107 */,_AB/* FormStructure.Chapter3.ch3DataUsage12 */),
_AD/* ch3DataUsage174 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_AE/* ch3DataUsage173 */ = new T2(1,_AD/* FormStructure.Chapter3.ch3DataUsage174 */,_I/* GHC.Types.[] */),
_AF/* ch3DataUsage175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_AG/* ch3DataUsage172 */ = new T2(1,_AF/* FormStructure.Chapter3.ch3DataUsage175 */,_AE/* FormStructure.Chapter3.ch3DataUsage173 */),
_AH/* ch3DataUsage176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_AI/* ch3DataUsage171 */ = new T2(1,_AH/* FormStructure.Chapter3.ch3DataUsage176 */,_AG/* FormStructure.Chapter3.ch3DataUsage172 */),
_AJ/* ch3DataUsage177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_AK/* ch3DataUsage170 */ = new T2(1,_AJ/* FormStructure.Chapter3.ch3DataUsage177 */,_AI/* FormStructure.Chapter3.ch3DataUsage171 */),
_AL/* ch3DataUsage169 */ = new T1(1,_AK/* FormStructure.Chapter3.ch3DataUsage170 */),
_AM/* ch3DataUsage179 */ = new T2(1,_pY/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_AN/* ch3DataUsage181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_AO/* ch3DataUsage180 */ = new T1(1,_AN/* FormStructure.Chapter3.ch3DataUsage181 */),
_AP/* ch3DataUsage183 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_AQ/* ch3DataUsage182 */ = new T2(1,_AP/* FormStructure.Chapter3.ch3DataUsage183 */,_I/* GHC.Types.[] */),
_AR/* ch3DataUsage185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_AS/* ch3DataUsage184 */ = new T1(1,_AR/* FormStructure.Chapter3.ch3DataUsage185 */),
_AT/* ch3DataUsage187 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_AU/* ch3DataUsage186 */ = new T1(1,_AT/* FormStructure.Chapter3.ch3DataUsage187 */),
_AV/* ch3DataUsage178 */ = {_:0,a:_AU/* FormStructure.Chapter3.ch3DataUsage186 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_AS/* FormStructure.Chapter3.ch3DataUsage184 */,d:_AQ/* FormStructure.Chapter3.ch3DataUsage182 */,e:_AO/* FormStructure.Chapter3.ch3DataUsage180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_AM/* FormStructure.Chapter3.ch3DataUsage179 */},
_AW/* ch3DataUsage168 */ = new T2(3,_AV/* FormStructure.Chapter3.ch3DataUsage178 */,_AL/* FormStructure.Chapter3.ch3DataUsage169 */),
_AX/* ch3DataUsage167 */ = new T2(1,_AW/* FormStructure.Chapter3.ch3DataUsage168 */,_I/* GHC.Types.[] */),
_AY/* ch3DataUsage190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_AZ/* ch3DataUsage189 */ = new T1(1,_AY/* FormStructure.Chapter3.ch3DataUsage190 */),
_B0/* ch3DataUsage188 */ = {_:0,a:_AZ/* FormStructure.Chapter3.ch3DataUsage189 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_B1/* ch3DataUsage166 */ = new T3(7,_B0/* FormStructure.Chapter3.ch3DataUsage188 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_AX/* FormStructure.Chapter3.ch3DataUsage167 */),
_B2/* ch3DataUsage10 */ = new T2(1,_B1/* FormStructure.Chapter3.ch3DataUsage166 */,_AC/* FormStructure.Chapter3.ch3DataUsage11 */),
_B3/* ch3DataUsage207 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-sum"));
}),
_B4/* ch3DataUsage206 */ = new T1(1,_B3/* FormStructure.Chapter3.ch3DataUsage207 */),
_B5/* ch3DataUsage205 */ = {_:0,a:_yb/* FormStructure.Chapter3.ch3DataUsage30 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_B4/* FormStructure.Chapter3.ch3DataUsage206 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_y9/* FormStructure.Chapter3.ch3DataUsage24 */},
_B6/* ch3DataUsage204 */ = new T2(3,_B5/* FormStructure.Chapter3.ch3DataUsage205 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_B7/* ch3DataUsage203 */ = new T2(1,_B6/* FormStructure.Chapter3.ch3DataUsage204 */,_I/* GHC.Types.[] */),
_B8/* ch3DataUsage215 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-worldwide"));
}),
_B9/* ch3DataUsage214 */ = new T2(1,_B8/* FormStructure.Chapter3.ch3DataUsage215 */,_I/* GHC.Types.[] */),
_Ba/* ch3DataUsage216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-european"));
}),
_Bb/* ch3DataUsage213 */ = new T2(1,_Ba/* FormStructure.Chapter3.ch3DataUsage216 */,_B9/* FormStructure.Chapter3.ch3DataUsage214 */),
_Bc/* ch3DataUsage217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-national"));
}),
_Bd/* ch3DataUsage212 */ = new T2(1,_Bc/* FormStructure.Chapter3.ch3DataUsage217 */,_Bb/* FormStructure.Chapter3.ch3DataUsage213 */),
_Be/* ch3DataUsage218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-institutional"));
}),
_Bf/* ch3DataUsage211 */ = new T2(1,_Be/* FormStructure.Chapter3.ch3DataUsage218 */,_Bd/* FormStructure.Chapter3.ch3DataUsage212 */),
_Bg/* ch3DataUsage_fundingSumRule1 */ = new T2(0,_Bf/* FormStructure.Chapter3.ch3DataUsage211 */,_B3/* FormStructure.Chapter3.ch3DataUsage207 */),
_Bh/* ch3DataUsage210 */ = new T2(1,_Bg/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule1 */,_yl/* FormStructure.Chapter3.ch3DataUsage123 */),
_Bi/* ch3DataUsage219 */ = new T1(1,_B8/* FormStructure.Chapter3.ch3DataUsage215 */),
_Bj/* ch3DataUsage209 */ = {_:0,a:_yy/* FormStructure.Chapter3.ch3DataUsage135 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Bi/* FormStructure.Chapter3.ch3DataUsage219 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Bh/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bk/* ch3DataUsage208 */ = new T2(3,_Bj/* FormStructure.Chapter3.ch3DataUsage209 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bl/* ch3DataUsage202 */ = new T2(1,_Bk/* FormStructure.Chapter3.ch3DataUsage208 */,_B7/* FormStructure.Chapter3.ch3DataUsage203 */),
_Bm/* ch3DataUsage222 */ = new T1(1,_Ba/* FormStructure.Chapter3.ch3DataUsage216 */),
_Bn/* ch3DataUsage221 */ = {_:0,a:_yE/* FormStructure.Chapter3.ch3DataUsage140 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Bm/* FormStructure.Chapter3.ch3DataUsage222 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Bh/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bo/* ch3DataUsage220 */ = new T2(3,_Bn/* FormStructure.Chapter3.ch3DataUsage221 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bp/* ch3DataUsage201 */ = new T2(1,_Bo/* FormStructure.Chapter3.ch3DataUsage220 */,_Bl/* FormStructure.Chapter3.ch3DataUsage202 */),
_Bq/* ch3DataUsage225 */ = new T1(1,_Bc/* FormStructure.Chapter3.ch3DataUsage217 */),
_Br/* ch3DataUsage224 */ = {_:0,a:_yK/* FormStructure.Chapter3.ch3DataUsage145 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Bq/* FormStructure.Chapter3.ch3DataUsage225 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Bh/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bs/* ch3DataUsage223 */ = new T2(3,_Br/* FormStructure.Chapter3.ch3DataUsage224 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bt/* ch3DataUsage200 */ = new T2(1,_Bs/* FormStructure.Chapter3.ch3DataUsage223 */,_Bp/* FormStructure.Chapter3.ch3DataUsage201 */),
_Bu/* ch3DataUsage228 */ = new T1(1,_Be/* FormStructure.Chapter3.ch3DataUsage218 */),
_Bv/* ch3DataUsage227 */ = {_:0,a:_yQ/* FormStructure.Chapter3.ch3DataUsage150 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Bu/* FormStructure.Chapter3.ch3DataUsage228 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Bh/* FormStructure.Chapter3.ch3DataUsage210 */},
_Bw/* ch3DataUsage226 */ = new T2(3,_Bv/* FormStructure.Chapter3.ch3DataUsage227 */,_ye/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bx/* ch3DataUsage199 */ = new T2(1,_Bw/* FormStructure.Chapter3.ch3DataUsage226 */,_Bt/* FormStructure.Chapter3.ch3DataUsage200 */),
_By/* ch3DataUsage198 */ = new T3(7,_yW/* FormStructure.Chapter3.ch3DataUsage152 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_Bx/* FormStructure.Chapter3.ch3DataUsage199 */),
_Bz/* ch3DataUsage197 */ = new T2(1,_By/* FormStructure.Chapter3.ch3DataUsage198 */,_I/* GHC.Types.[] */),
_BA/* ch3DataUsage196 */ = new T2(1,_z4/* FormStructure.Chapter3.ch3DataUsage155 */,_Bz/* FormStructure.Chapter3.ch3DataUsage197 */),
_BB/* ch3DataUsage231 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_BC/* ch3DataUsage230 */ = new T1(1,_BB/* FormStructure.Chapter3.ch3DataUsage231 */),
_BD/* ch3DataUsage229 */ = {_:0,a:_BC/* FormStructure.Chapter3.ch3DataUsage230 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_BE/* ch3DataUsage195 */ = new T3(7,_BD/* FormStructure.Chapter3.ch3DataUsage229 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_BA/* FormStructure.Chapter3.ch3DataUsage196 */),
_BF/* ch3DataUsage194 */ = new T2(1,_BE/* FormStructure.Chapter3.ch3DataUsage195 */,_I/* GHC.Types.[] */),
_BG/* ch3DataUsage235 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_BH/* ch3DataUsage234 */ = new T1(1,_BG/* FormStructure.Chapter3.ch3DataUsage235 */),
_BI/* ch3DataUsage237 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_3"));
}),
_BJ/* ch3DataUsage236 */ = new T2(1,_BI/* FormStructure.Chapter3.ch3DataUsage237 */,_I/* GHC.Types.[] */),
_BK/* ch3DataUsage239 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific raw data volume"));
}),
_BL/* ch3DataUsage238 */ = new T1(1,_BK/* FormStructure.Chapter3.ch3DataUsage239 */),
_BM/* ch3DataUsage233 */ = {_:0,a:_BL/* FormStructure.Chapter3.ch3DataUsage238 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_BJ/* FormStructure.Chapter3.ch3DataUsage236 */,e:_BH/* FormStructure.Chapter3.ch3DataUsage234 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_BN/* ch3DataUsage232 */ = new T2(3,_BM/* FormStructure.Chapter3.ch3DataUsage233 */,_AL/* FormStructure.Chapter3.ch3DataUsage169 */),
_BO/* ch3DataUsage193 */ = new T2(1,_BN/* FormStructure.Chapter3.ch3DataUsage232 */,_BF/* FormStructure.Chapter3.ch3DataUsage194 */),
_BP/* ch3DataUsage241 */ = new T1(0,_AF/* FormStructure.Chapter3.ch3DataUsage175 */),
_BQ/* ch3DataUsage243 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_BR/* ch3DataUsage245 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_BS/* ch3DataUsage244 */ = new T2(1,_BR/* FormStructure.Chapter3.ch3DataUsage245 */,_I/* GHC.Types.[] */),
_BT/* ch3DataUsage247 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_BU/* ch3DataUsage246 */ = new T1(1,_BT/* FormStructure.Chapter3.ch3DataUsage247 */),
_BV/* ch3DataUsage249 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_BW/* ch3DataUsage248 */ = new T1(1,_BV/* FormStructure.Chapter3.ch3DataUsage249 */),
_BX/* ch3DataUsage242 */ = {_:0,a:_BW/* FormStructure.Chapter3.ch3DataUsage248 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_BU/* FormStructure.Chapter3.ch3DataUsage246 */,d:_BS/* FormStructure.Chapter3.ch3DataUsage244 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_BQ/* FormStructure.Chapter3.ch3DataUsage243 */},
_BY/* ch3DataUsage240 */ = new T2(3,_BX/* FormStructure.Chapter3.ch3DataUsage242 */,_BP/* FormStructure.Chapter3.ch3DataUsage241 */),
_BZ/* ch3DataUsage192 */ = new T2(1,_BY/* FormStructure.Chapter3.ch3DataUsage240 */,_BO/* FormStructure.Chapter3.ch3DataUsage193 */),
_C0/* ch3DataUsage252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_C1/* ch3DataUsage251 */ = new T1(1,_C0/* FormStructure.Chapter3.ch3DataUsage252 */),
_C2/* ch3DataUsage250 */ = {_:0,a:_C1/* FormStructure.Chapter3.ch3DataUsage251 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_C3/* ch3DataUsage191 */ = new T3(7,_C2/* FormStructure.Chapter3.ch3DataUsage250 */,_y1/* FormStructure.Chapter3.ch3DataUsage70 */,_BZ/* FormStructure.Chapter3.ch3DataUsage192 */),
_C4/* ch3DataUsage9 */ = new T2(1,_C3/* FormStructure.Chapter3.ch3DataUsage191 */,_B2/* FormStructure.Chapter3.ch3DataUsage10 */),
_C5/* ch3DataUsage8 */ = new T2(1,_y2/* FormStructure.Chapter3.ch3DataUsage253 */,_C4/* FormStructure.Chapter3.ch3DataUsage9 */),
_C6/* ch3DataUsage7 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_As/* FormStructure.Chapter3.ch3DataUsage98 */,_C5/* FormStructure.Chapter3.ch3DataUsage8 */),
_C7/* ch3DataUsage3 */ = new T2(1,_C6/* FormStructure.Chapter3.ch3DataUsage7 */,_xS/* FormStructure.Chapter3.ch3DataUsage4 */),
_C8/* ch3DataUsage2 */ = new T2(4,_xP/* FormStructure.Chapter3.ch3DataUsage262 */,_C7/* FormStructure.Chapter3.ch3DataUsage3 */),
_C9/* ch3DataUsage1 */ = new T2(1,_C8/* FormStructure.Chapter3.ch3DataUsage2 */,_I/* GHC.Types.[] */),
_Ca/* ch3DataUsage267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("3.Usage "));
}),
_Cb/* ch3DataUsage266 */ = new T1(1,_Ca/* FormStructure.Chapter3.ch3DataUsage267 */),
_Cc/* ch3DataUsage265 */ = {_:0,a:_Cb/* FormStructure.Chapter3.ch3DataUsage266 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Cd/* ch3DataUsage */ = new T2(6,_Cc/* FormStructure.Chapter3.ch3DataUsage265 */,_C9/* FormStructure.Chapter3.ch3DataUsage1 */),
_Ce/* ch4DataStorage3 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_Cf/* ch4DataStorage46 */ = 0,
_Cg/* ch4DataStorage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage providers"));
}),
_Ch/* ch4DataStorage48 */ = new T1(1,_Cg/* FormStructure.Chapter4.ch4DataStorage49 */),
_Ci/* ch4DataStorage47 */ = {_:0,a:_Ch/* FormStructure.Chapter4.ch4DataStorage48 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Cj/* ch4DataStorage11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_Ck/* ch4DataStorage10 */ = new T1(0,_Cj/* FormStructure.Chapter4.ch4DataStorage11 */),
_Cl/* ch4DataStorage26 */ = function(_Cm/* sf2j */){
  var _Cn/* sf2k */ = E(_Cm/* sf2j */);
  return (_Cn/* sf2k */<0) ? false : _Cn/* sf2k */<=100;
},
_Co/* ch4DataStorage25 */ = new T1(4,_Cl/* FormStructure.Chapter4.ch4DataStorage26 */),
_Cp/* ch4DataStorage24 */ = new T2(1,_Co/* FormStructure.Chapter4.ch4DataStorage25 */,_I/* GHC.Types.[] */),
_Cq/* ch4DataStorage18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-providers-sum"));
}),
_Cr/* ch4DataStorage30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-external"));
}),
_Cs/* ch4DataStorage29 */ = new T2(1,_Cr/* FormStructure.Chapter4.ch4DataStorage30 */,_I/* GHC.Types.[] */),
_Ct/* ch4DataStorage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-institutional"));
}),
_Cu/* ch4DataStorage28 */ = new T2(1,_Ct/* FormStructure.Chapter4.ch4DataStorage31 */,_Cs/* FormStructure.Chapter4.ch4DataStorage29 */),
_Cv/* ch4DataStorage32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-group"));
}),
_Cw/* ch4DataStorage27 */ = new T2(1,_Cv/* FormStructure.Chapter4.ch4DataStorage32 */,_Cu/* FormStructure.Chapter4.ch4DataStorage28 */),
_Cx/* ch4DataStorage_storageSumRule */ = new T2(0,_Cw/* FormStructure.Chapter4.ch4DataStorage27 */,_Cq/* FormStructure.Chapter4.ch4DataStorage18 */),
_Cy/* ch4DataStorage23 */ = new T2(1,_Cx/* FormStructure.Chapter4.ch4DataStorage_storageSumRule */,_Cp/* FormStructure.Chapter4.ch4DataStorage24 */),
_Cz/* ch4DataStorage43 */ = new T1(1,_Cv/* FormStructure.Chapter4.ch4DataStorage32 */),
_CA/* ch4DataStorage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Group\'s local"));
}),
_CB/* ch4DataStorage44 */ = new T1(1,_CA/* FormStructure.Chapter4.ch4DataStorage45 */),
_CC/* ch4DataStorage42 */ = {_:0,a:_CB/* FormStructure.Chapter4.ch4DataStorage44 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Cz/* FormStructure.Chapter4.ch4DataStorage43 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Cy/* FormStructure.Chapter4.ch4DataStorage23 */},
_CD/* ch4DataStorage41 */ = new T2(3,_CC/* FormStructure.Chapter4.ch4DataStorage42 */,_Ck/* FormStructure.Chapter4.ch4DataStorage10 */),
_CE/* ch4DataStorage38 */ = new T1(1,_Ct/* FormStructure.Chapter4.ch4DataStorage31 */),
_CF/* ch4DataStorage40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_CG/* ch4DataStorage39 */ = new T1(1,_CF/* FormStructure.Chapter4.ch4DataStorage40 */),
_CH/* ch4DataStorage37 */ = {_:0,a:_CG/* FormStructure.Chapter4.ch4DataStorage39 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_CE/* FormStructure.Chapter4.ch4DataStorage38 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Cy/* FormStructure.Chapter4.ch4DataStorage23 */},
_CI/* ch4DataStorage36 */ = new T2(3,_CH/* FormStructure.Chapter4.ch4DataStorage37 */,_Ck/* FormStructure.Chapter4.ch4DataStorage10 */),
_CJ/* ch4DataStorage33 */ = new T1(1,_Cr/* FormStructure.Chapter4.ch4DataStorage30 */),
_CK/* ch4DataStorage35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External Provider"));
}),
_CL/* ch4DataStorage34 */ = new T1(1,_CK/* FormStructure.Chapter4.ch4DataStorage35 */),
_CM/* ch4DataStorage22 */ = {_:0,a:_CL/* FormStructure.Chapter4.ch4DataStorage34 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_CJ/* FormStructure.Chapter4.ch4DataStorage33 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_Cy/* FormStructure.Chapter4.ch4DataStorage23 */},
_CN/* ch4DataStorage21 */ = new T2(3,_CM/* FormStructure.Chapter4.ch4DataStorage22 */,_Ck/* FormStructure.Chapter4.ch4DataStorage10 */),
_CO/* ch4DataStorage16 */ = function(_CP/* sf2p */){
  return (E(_CP/* sf2p */)==100) ? true : false;
},
_CQ/* ch4DataStorage15 */ = new T1(4,_CO/* FormStructure.Chapter4.ch4DataStorage16 */),
_CR/* ch4DataStorage14 */ = new T2(1,_CQ/* FormStructure.Chapter4.ch4DataStorage15 */,_I/* GHC.Types.[] */),
_CS/* ch4DataStorage13 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_CR/* FormStructure.Chapter4.ch4DataStorage14 */),
_CT/* ch4DataStorage17 */ = new T1(1,_Cq/* FormStructure.Chapter4.ch4DataStorage18 */),
_CU/* ch4DataStorage20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_CV/* ch4DataStorage19 */ = new T1(1,_CU/* FormStructure.Chapter4.ch4DataStorage20 */),
_CW/* ch4DataStorage12 */ = {_:0,a:_CV/* FormStructure.Chapter4.ch4DataStorage19 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_CT/* FormStructure.Chapter4.ch4DataStorage17 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_CS/* FormStructure.Chapter4.ch4DataStorage13 */},
_CX/* ch4DataStorage9 */ = new T2(3,_CW/* FormStructure.Chapter4.ch4DataStorage12 */,_Ck/* FormStructure.Chapter4.ch4DataStorage10 */),
_CY/* ch4DataStorage8 */ = new T2(1,_CX/* FormStructure.Chapter4.ch4DataStorage9 */,_I/* GHC.Types.[] */),
_CZ/* ch4DataStorage7 */ = new T2(1,_CN/* FormStructure.Chapter4.ch4DataStorage21 */,_CY/* FormStructure.Chapter4.ch4DataStorage8 */),
_D0/* ch4DataStorage6 */ = new T2(1,_CI/* FormStructure.Chapter4.ch4DataStorage36 */,_CZ/* FormStructure.Chapter4.ch4DataStorage7 */),
_D1/* ch4DataStorage5 */ = new T2(1,_CD/* FormStructure.Chapter4.ch4DataStorage41 */,_D0/* FormStructure.Chapter4.ch4DataStorage6 */),
_D2/* ch4DataStorage4 */ = new T3(7,_Ci/* FormStructure.Chapter4.ch4DataStorage47 */,_Cf/* FormStructure.Chapter4.ch4DataStorage46 */,_D1/* FormStructure.Chapter4.ch4DataStorage5 */),
_D3/* ch4DataStorage2 */ = new T2(1,_D2/* FormStructure.Chapter4.ch4DataStorage4 */,_Ce/* FormStructure.Chapter4.ch4DataStorage3 */),
_D4/* ch4DataStorage60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_D5/* ch4DataStorage59 */ = new T2(1,_D4/* FormStructure.Chapter4.ch4DataStorage60 */,_I/* GHC.Types.[] */),
_D6/* ch4DataStorage61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_D7/* ch4DataStorage58 */ = new T2(1,_D6/* FormStructure.Chapter4.ch4DataStorage61 */,_D5/* FormStructure.Chapter4.ch4DataStorage59 */),
_D8/* ch4DataStorage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_D9/* ch4DataStorage57 */ = new T2(1,_D8/* FormStructure.Chapter4.ch4DataStorage62 */,_D7/* FormStructure.Chapter4.ch4DataStorage58 */),
_Da/* ch4DataStorage63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_Db/* ch4DataStorage56 */ = new T2(1,_Da/* FormStructure.Chapter4.ch4DataStorage63 */,_D9/* FormStructure.Chapter4.ch4DataStorage57 */),
_Dc/* ch4DataStorage55 */ = new T1(1,_Db/* FormStructure.Chapter4.ch4DataStorage56 */),
_Dd/* ch4DataStorage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of backups"));
}),
_De/* ch4DataStorage65 */ = new T1(1,_Dd/* FormStructure.Chapter4.ch4DataStorage66 */),
_Df/* ch4DataStorage64 */ = {_:0,a:_De/* FormStructure.Chapter4.ch4DataStorage65 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Dg/* ch4DataStorage54 */ = new T2(3,_Df/* FormStructure.Chapter4.ch4DataStorage64 */,_Dc/* FormStructure.Chapter4.ch4DataStorage55 */),
_Dh/* ch4DataStorage53 */ = new T2(1,_Dg/* FormStructure.Chapter4.ch4DataStorage54 */,_I/* GHC.Types.[] */),
_Di/* ch4DataStorage70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of data stored at the end of 2015"));
}),
_Dj/* ch4DataStorage69 */ = new T1(1,_Di/* FormStructure.Chapter4.ch4DataStorage70 */),
_Dk/* ch4DataStorage68 */ = {_:0,a:_Dj/* FormStructure.Chapter4.ch4DataStorage69 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Dl/* ch4DataStorage67 */ = new T2(3,_Dk/* FormStructure.Chapter4.ch4DataStorage68 */,_Dc/* FormStructure.Chapter4.ch4DataStorage55 */),
_Dm/* ch4DataStorage52 */ = new T2(1,_Dl/* FormStructure.Chapter4.ch4DataStorage67 */,_Dh/* FormStructure.Chapter4.ch4DataStorage53 */),
_Dn/* ch4DataStorage72 */ = new T1(0,_D6/* FormStructure.Chapter4.ch4DataStorage61 */),
_Do/* ch4DataStorage74 */ = new T2(1,_pC/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_Dp/* ch4DataStorage76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_Dq/* ch4DataStorage75 */ = new T1(1,_Dp/* FormStructure.Chapter4.ch4DataStorage76 */),
_Dr/* ch4DataStorage78 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume produced in 2015"));
}),
_Ds/* ch4DataStorage77 */ = new T1(1,_Dr/* FormStructure.Chapter4.ch4DataStorage78 */),
_Dt/* ch4DataStorage73 */ = {_:0,a:_Ds/* FormStructure.Chapter4.ch4DataStorage77 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_Dq/* FormStructure.Chapter4.ch4DataStorage75 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_Do/* FormStructure.Chapter4.ch4DataStorage74 */},
_Du/* ch4DataStorage71 */ = new T2(3,_Dt/* FormStructure.Chapter4.ch4DataStorage73 */,_Dn/* FormStructure.Chapter4.ch4DataStorage72 */),
_Dv/* ch4DataStorage51 */ = new T2(1,_Du/* FormStructure.Chapter4.ch4DataStorage71 */,_Dm/* FormStructure.Chapter4.ch4DataStorage52 */),
_Dw/* ch4DataStorage81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just scientic data volumes (without backups and scratch/tmp) are in question."));
}),
_Dx/* ch4DataStorage80 */ = new T1(1,_Dw/* FormStructure.Chapter4.ch4DataStorage81 */),
_Dy/* ch4DataStorage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data volumes"));
}),
_Dz/* ch4DataStorage82 */ = new T1(1,_Dy/* FormStructure.Chapter4.ch4DataStorage83 */),
_DA/* ch4DataStorage79 */ = {_:0,a:_Dz/* FormStructure.Chapter4.ch4DataStorage82 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Dx/* FormStructure.Chapter4.ch4DataStorage80 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_DB/* ch4DataStorage50 */ = new T3(7,_DA/* FormStructure.Chapter4.ch4DataStorage79 */,_Cf/* FormStructure.Chapter4.ch4DataStorage46 */,_Dv/* FormStructure.Chapter4.ch4DataStorage51 */),
_DC/* ch4DataStorage1 */ = new T2(1,_DB/* FormStructure.Chapter4.ch4DataStorage50 */,_D3/* FormStructure.Chapter4.ch4DataStorage2 */),
_DD/* ch4DataStorage86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("4.Storage "));
}),
_DE/* ch4DataStorage85 */ = new T1(1,_DD/* FormStructure.Chapter4.ch4DataStorage86 */),
_DF/* ch4DataStorage84 */ = {_:0,a:_DE/* FormStructure.Chapter4.ch4DataStorage85 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_DG/* ch4DataStorage */ = new T2(6,_DF/* FormStructure.Chapter4.ch4DataStorage84 */,_DC/* FormStructure.Chapter4.ch4DataStorage1 */),
_DH/* ch5DataAccessibility2 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_DI/* ch5DataAccessibility32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you provide data accessibility for external parties?"));
}),
_DJ/* ch5DataAccessibility31 */ = new T1(1,_DI/* FormStructure.Chapter5.ch5DataAccessibility32 */),
_DK/* ch5DataAccessibility30 */ = {_:0,a:_DJ/* FormStructure.Chapter5.ch5DataAccessibility31 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_DL/* ch5DataAccessibility7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_DM/* ch5DataAccessibility6 */ = new T1(0,_DL/* FormStructure.Chapter5.ch5DataAccessibility7 */),
_DN/* ch5DataAccessibility5 */ = new T2(1,_DM/* FormStructure.Chapter5.ch5DataAccessibility6 */,_I/* GHC.Types.[] */),
_DO/* ch5DataAccessibility29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_DP/* ch5DataAccessibility16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("URLs to web pages / data source or other accessibility link"));
}),
_DQ/* ch5DataAccessibility15 */ = new T1(1,_DP/* FormStructure.Chapter5.ch5DataAccessibility16 */),
_DR/* ch5DataAccessibility18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Links to your services"));
}),
_DS/* ch5DataAccessibility17 */ = new T1(1,_DR/* FormStructure.Chapter5.ch5DataAccessibility18 */),
_DT/* ch5DataAccessibility14 */ = {_:0,a:_DS/* FormStructure.Chapter5.ch5DataAccessibility17 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_DQ/* FormStructure.Chapter5.ch5DataAccessibility15 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_DU/* ch5DataAccessibility13 */ = new T1(1,_DT/* FormStructure.Chapter5.ch5DataAccessibility14 */),
_DV/* ch5DataAccessibility12 */ = new T2(1,_DU/* FormStructure.Chapter5.ch5DataAccessibility13 */,_I/* GHC.Types.[] */),
_DW/* ch5DataAccessibility22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For inspiration, click the red box in the figure"));
}),
_DX/* ch5DataAccessibility21 */ = new T1(1,_DW/* FormStructure.Chapter5.ch5DataAccessibility22 */),
_DY/* ch5DataAccessibility24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How do you make your data accessible?"));
}),
_DZ/* ch5DataAccessibility23 */ = new T1(1,_DY/* FormStructure.Chapter5.ch5DataAccessibility24 */),
_E0/* ch5DataAccessibility20 */ = {_:0,a:_DZ/* FormStructure.Chapter5.ch5DataAccessibility23 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_DX/* FormStructure.Chapter5.ch5DataAccessibility21 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_E1/* ch5DataAccessibility19 */ = new T1(1,_E0/* FormStructure.Chapter5.ch5DataAccessibility20 */),
_E2/* ch5DataAccessibility11 */ = new T2(1,_E1/* FormStructure.Chapter5.ch5DataAccessibility19 */,_DV/* FormStructure.Chapter5.ch5DataAccessibility12 */),
_E3/* ch5DataAccessibility25 */ = 1,
_E4/* ch5DataAccessibility28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accessibility details"));
}),
_E5/* ch5DataAccessibility27 */ = new T1(1,_E4/* FormStructure.Chapter5.ch5DataAccessibility28 */),
_E6/* ch5DataAccessibility26 */ = {_:0,a:_E5/* FormStructure.Chapter5.ch5DataAccessibility27 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_E7/* ch5DataAccessibility10 */ = new T3(7,_E6/* FormStructure.Chapter5.ch5DataAccessibility26 */,_E3/* FormStructure.Chapter5.ch5DataAccessibility25 */,_E2/* FormStructure.Chapter5.ch5DataAccessibility11 */),
_E8/* ch5DataAccessibility9 */ = new T2(1,_E7/* FormStructure.Chapter5.ch5DataAccessibility10 */,_I/* GHC.Types.[] */),
_E9/* ch5DataAccessibility8 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_DO/* FormStructure.Chapter5.ch5DataAccessibility29 */,_E8/* FormStructure.Chapter5.ch5DataAccessibility9 */),
_Ea/* ch5DataAccessibility4 */ = new T2(1,_E9/* FormStructure.Chapter5.ch5DataAccessibility8 */,_DN/* FormStructure.Chapter5.ch5DataAccessibility5 */),
_Eb/* ch5DataAccessibility3 */ = new T2(4,_DK/* FormStructure.Chapter5.ch5DataAccessibility30 */,_Ea/* FormStructure.Chapter5.ch5DataAccessibility4 */),
_Ec/* ch5DataAccessibility1 */ = new T2(1,_Eb/* FormStructure.Chapter5.ch5DataAccessibility3 */,_DH/* FormStructure.Chapter5.ch5DataAccessibility2 */),
_Ed/* ch5DataAccessibility35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("5.Accessibility "));
}),
_Ee/* ch5DataAccessibility34 */ = new T1(1,_Ed/* FormStructure.Chapter5.ch5DataAccessibility35 */),
_Ef/* ch5DataAccessibility33 */ = {_:0,a:_Ee/* FormStructure.Chapter5.ch5DataAccessibility34 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Eg/* ch5DataAccessibility */ = new T2(6,_Ef/* FormStructure.Chapter5.ch5DataAccessibility33 */,_Ec/* FormStructure.Chapter5.ch5DataAccessibility1 */),
_Eh/* ch6DataManagement13 */ = 0,
_Ei/* ch6DataManagement28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_Ej/* ch6DataManagement27 */ = new T1(0,_Ei/* FormStructure.Chapter6.ch6DataManagement28 */),
_Ek/* ch6DataManagement26 */ = new T2(1,_Ej/* FormStructure.Chapter6.ch6DataManagement27 */,_I/* GHC.Types.[] */),
_El/* xhow3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How?"));
}),
_Em/* xhow2 */ = new T1(1,_El/* FormStructure.Common.xhow3 */),
_En/* xhow1 */ = {_:0,a:_Em/* FormStructure.Common.xhow2 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Eo/* xhow */ = new T1(1,_En/* FormStructure.Common.xhow1 */),
_Ep/* ch6DataManagement30 */ = new T2(1,_Eo/* FormStructure.Common.xhow */,_I/* GHC.Types.[] */),
_Eq/* ch6DataManagement31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_Er/* ch6DataManagement29 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_Eq/* FormStructure.Chapter6.ch6DataManagement31 */,_Ep/* FormStructure.Chapter6.ch6DataManagement30 */),
_Es/* ch6DataManagement25 */ = new T2(1,_Er/* FormStructure.Chapter6.ch6DataManagement29 */,_Ek/* FormStructure.Chapter6.ch6DataManagement26 */),
_Et/* ch6DataManagement34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you apply some form of data stewardship?"));
}),
_Eu/* ch6DataManagement33 */ = new T1(1,_Et/* FormStructure.Chapter6.ch6DataManagement34 */),
_Ev/* ch6DataManagement32 */ = {_:0,a:_Eu/* FormStructure.Chapter6.ch6DataManagement33 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ew/* ch6DataManagement24 */ = new T2(4,_Ev/* FormStructure.Chapter6.ch6DataManagement32 */,_Es/* FormStructure.Chapter6.ch6DataManagement25 */),
_Ex/* ch6DataManagement23 */ = new T2(1,_Ew/* FormStructure.Chapter6.ch6DataManagement24 */,_I/* GHC.Types.[] */),
_Ey/* ch6DataManagement37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_Ez/* ch6DataManagement36 */ = new T1(0,_Ey/* FormStructure.Chapter6.ch6DataManagement37 */),
_EA/* ch6DataManagement40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest required sustainability"));
}),
_EB/* ch6DataManagement39 */ = new T1(1,_EA/* FormStructure.Chapter6.ch6DataManagement40 */),
_EC/* ch6DataManagement38 */ = {_:0,a:_EB/* FormStructure.Chapter6.ch6DataManagement39 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_ED/* ch6DataManagement35 */ = new T2(3,_EC/* FormStructure.Chapter6.ch6DataManagement38 */,_Ez/* FormStructure.Chapter6.ch6DataManagement36 */),
_EE/* ch6DataManagement22 */ = new T2(1,_ED/* FormStructure.Chapter6.ch6DataManagement35 */,_Ex/* FormStructure.Chapter6.ch6DataManagement23 */),
_EF/* ch6DataManagement51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long"));
}),
_EG/* ch6DataManagement50 */ = new T1(1,_EF/* FormStructure.Chapter6.ch6DataManagement51 */),
_EH/* ch6DataManagement49 */ = {_:0,a:_EG/* FormStructure.Chapter6.ch6DataManagement50 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EI/* ch6DataManagement48 */ = new T2(3,_EH/* FormStructure.Chapter6.ch6DataManagement49 */,_Ez/* FormStructure.Chapter6.ch6DataManagement36 */),
_EJ/* ch6DataManagement47 */ = new T2(1,_EI/* FormStructure.Chapter6.ch6DataManagement48 */,_I/* GHC.Types.[] */),
_EK/* ch6DataManagement52 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EL/* ch6DataManagement46 */ = new T3(7,_EK/* FormStructure.Chapter6.ch6DataManagement52 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_EJ/* FormStructure.Chapter6.ch6DataManagement47 */),
_EM/* ch6DataManagement45 */ = new T2(1,_EL/* FormStructure.Chapter6.ch6DataManagement46 */,_I/* GHC.Types.[] */),
_EN/* ch6DataManagement53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("short-term"));
}),
_EO/* ch6DataManagement44 */ = new T3(1,_89/* FormEngine.FormItem.NoNumbering */,_EN/* FormStructure.Chapter6.ch6DataManagement53 */,_EM/* FormStructure.Chapter6.ch6DataManagement45 */),
_EP/* ch6DataManagement43 */ = new T2(1,_EO/* FormStructure.Chapter6.ch6DataManagement44 */,_I/* GHC.Types.[] */),
_EQ/* ch6DataManagement55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("long-term, continuous funding"));
}),
_ER/* ch6DataManagement54 */ = new T1(0,_EQ/* FormStructure.Chapter6.ch6DataManagement55 */),
_ES/* ch6DataManagement42 */ = new T2(1,_ER/* FormStructure.Chapter6.ch6DataManagement54 */,_EP/* FormStructure.Chapter6.ch6DataManagement43 */),
_ET/* ch6DataManagement58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sustainability"));
}),
_EU/* ch6DataManagement57 */ = new T1(1,_ET/* FormStructure.Chapter6.ch6DataManagement58 */),
_EV/* ch6DataManagement56 */ = {_:0,a:_EU/* FormStructure.Chapter6.ch6DataManagement57 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EW/* ch6DataManagement41 */ = new T2(4,_EV/* FormStructure.Chapter6.ch6DataManagement56 */,_ES/* FormStructure.Chapter6.ch6DataManagement42 */),
_EX/* ch6DataManagement21 */ = new T2(1,_EW/* FormStructure.Chapter6.ch6DataManagement41 */,_EE/* FormStructure.Chapter6.ch6DataManagement22 */),
_EY/* ch6DataManagement63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("yes"));
}),
_EZ/* ch6DataManagement62 */ = new T1(0,_EY/* FormStructure.Chapter6.ch6DataManagement63 */),
_F0/* ch6DataManagement61 */ = new T2(1,_EZ/* FormStructure.Chapter6.ch6DataManagement62 */,_I/* GHC.Types.[] */),
_F1/* ch6DataManagement65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("no"));
}),
_F2/* ch6DataManagement64 */ = new T1(0,_F1/* FormStructure.Chapter6.ch6DataManagement65 */),
_F3/* ch6DataManagement60 */ = new T2(1,_F2/* FormStructure.Chapter6.ch6DataManagement64 */,_F0/* FormStructure.Chapter6.ch6DataManagement61 */),
_F4/* ch6DataManagement68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is data actuality maintained (updates)?"));
}),
_F5/* ch6DataManagement67 */ = new T1(1,_F4/* FormStructure.Chapter6.ch6DataManagement68 */),
_F6/* ch6DataManagement66 */ = {_:0,a:_F5/* FormStructure.Chapter6.ch6DataManagement67 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_F7/* ch6DataManagement59 */ = new T2(4,_F6/* FormStructure.Chapter6.ch6DataManagement66 */,_F3/* FormStructure.Chapter6.ch6DataManagement60 */),
_F8/* ch6DataManagement20 */ = new T2(1,_F7/* FormStructure.Chapter6.ch6DataManagement59 */,_EX/* FormStructure.Chapter6.ch6DataManagement21 */),
_F9/* ch6DataManagement72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you manage versioning?"));
}),
_Fa/* ch6DataManagement71 */ = new T1(1,_F9/* FormStructure.Chapter6.ch6DataManagement72 */),
_Fb/* ch6DataManagement70 */ = {_:0,a:_Fa/* FormStructure.Chapter6.ch6DataManagement71 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fc/* ch6DataManagement69 */ = new T2(4,_Fb/* FormStructure.Chapter6.ch6DataManagement70 */,_F3/* FormStructure.Chapter6.ch6DataManagement60 */),
_Fd/* ch6DataManagement19 */ = new T2(1,_Fc/* FormStructure.Chapter6.ch6DataManagement69 */,_F8/* FormStructure.Chapter6.ch6DataManagement20 */),
_Fe/* ch6DataManagement76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you handle error reports?"));
}),
_Ff/* ch6DataManagement75 */ = new T1(1,_Fe/* FormStructure.Chapter6.ch6DataManagement76 */),
_Fg/* ch6DataManagement74 */ = {_:0,a:_Ff/* FormStructure.Chapter6.ch6DataManagement75 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fh/* ch6DataManagement73 */ = new T2(4,_Fg/* FormStructure.Chapter6.ch6DataManagement74 */,_F3/* FormStructure.Chapter6.ch6DataManagement60 */),
_Fi/* ch6DataManagement18 */ = new T2(1,_Fh/* FormStructure.Chapter6.ch6DataManagement73 */,_Fd/* FormStructure.Chapter6.ch6DataManagement19 */),
_Fj/* ch6DataManagement79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Management details"));
}),
_Fk/* ch6DataManagement78 */ = new T1(1,_Fj/* FormStructure.Chapter6.ch6DataManagement79 */),
_Fl/* ch6DataManagement77 */ = {_:0,a:_Fk/* FormStructure.Chapter6.ch6DataManagement78 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fm/* ch6DataManagement17 */ = new T3(7,_Fl/* FormStructure.Chapter6.ch6DataManagement77 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_Fi/* FormStructure.Chapter6.ch6DataManagement18 */),
_Fn/* ch6DataManagement4 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_Fo/* ch6DataManagement16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total cost of data management"));
}),
_Fp/* ch6DataManagement15 */ = new T1(1,_Fo/* FormStructure.Chapter6.ch6DataManagement16 */),
_Fq/* ch6DataManagement14 */ = {_:0,a:_Fp/* FormStructure.Chapter6.ch6DataManagement15 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Fr/* ch6DataManagement12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_Fs/* ch6DataManagement11 */ = new T1(1,_Fr/* FormStructure.Chapter6.ch6DataManagement12 */),
_Ft/* ch6DataManagement10 */ = {_:0,a:_Fs/* FormStructure.Chapter6.ch6DataManagement11 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Fu/* ch6DataManagement9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_Fv/* ch6DataManagement8 */ = new T1(0,_Fu/* FormStructure.Chapter6.ch6DataManagement9 */),
_Fw/* ch6DataManagement7 */ = new T2(3,_Ft/* FormStructure.Chapter6.ch6DataManagement10 */,_Fv/* FormStructure.Chapter6.ch6DataManagement8 */),
_Fx/* ch6DataManagement6 */ = new T2(1,_Fw/* FormStructure.Chapter6.ch6DataManagement7 */,_I/* GHC.Types.[] */),
_Fy/* ch6DataManagement5 */ = new T3(7,_Fq/* FormStructure.Chapter6.ch6DataManagement14 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_Fx/* FormStructure.Chapter6.ch6DataManagement6 */),
_Fz/* ch6DataManagement3 */ = new T2(1,_Fy/* FormStructure.Chapter6.ch6DataManagement5 */,_Fn/* FormStructure.Chapter6.ch6DataManagement4 */),
_FA/* ch6DataManagement2 */ = new T2(1,_Fm/* FormStructure.Chapter6.ch6DataManagement17 */,_Fz/* FormStructure.Chapter6.ch6DataManagement3 */),
_FB/* ch6DataManagement86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("community use"));
}),
_FC/* ch6DataManagement85 */ = new T1(1,_FB/* FormStructure.Chapter6.ch6DataManagement86 */),
_FD/* ch6DataManagement84 */ = {_:0,a:_FC/* FormStructure.Chapter6.ch6DataManagement85 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FE/* ch6DataManagement83 */ = new T3(8,_FD/* FormStructure.Chapter6.ch6DataManagement84 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_FF/* ch6DataManagement82 */ = new T2(1,_FE/* FormStructure.Chapter6.ch6DataManagement83 */,_I/* GHC.Types.[] */),
_FG/* ch6DataManagement90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("local use"));
}),
_FH/* ch6DataManagement89 */ = new T1(1,_FG/* FormStructure.Chapter6.ch6DataManagement90 */),
_FI/* ch6DataManagement88 */ = {_:0,a:_FH/* FormStructure.Chapter6.ch6DataManagement89 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FJ/* ch6DataManagement87 */ = new T3(8,_FI/* FormStructure.Chapter6.ch6DataManagement88 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_FK/* ch6DataManagement81 */ = new T2(1,_FJ/* FormStructure.Chapter6.ch6DataManagement87 */,_FF/* FormStructure.Chapter6.ch6DataManagement82 */),
_FL/* ch6DataManagement93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We perform data management for:"));
}),
_FM/* ch6DataManagement92 */ = new T1(1,_FL/* FormStructure.Chapter6.ch6DataManagement93 */),
_FN/* ch6DataManagement91 */ = {_:0,a:_FM/* FormStructure.Chapter6.ch6DataManagement92 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FO/* ch6DataManagement80 */ = new T3(7,_FN/* FormStructure.Chapter6.ch6DataManagement91 */,_Eh/* FormStructure.Chapter6.ch6DataManagement13 */,_FK/* FormStructure.Chapter6.ch6DataManagement81 */),
_FP/* ch6DataManagement1 */ = new T2(1,_FO/* FormStructure.Chapter6.ch6DataManagement80 */,_FA/* FormStructure.Chapter6.ch6DataManagement2 */),
_FQ/* ch6DataManagement96 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("6.Management "));
}),
_FR/* ch6DataManagement95 */ = new T1(1,_FQ/* FormStructure.Chapter6.ch6DataManagement96 */),
_FS/* ch6DataManagement94 */ = {_:0,a:_FR/* FormStructure.Chapter6.ch6DataManagement95 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_FT/* ch6DataManagement */ = new T2(6,_FS/* FormStructure.Chapter6.ch6DataManagement94 */,_FP/* FormStructure.Chapter6.ch6DataManagement1 */),
_FU/* ch7Roles2 */ = new T2(1,_8k/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_FV/* ch7Roles13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Full-time equivalent"));
}),
_FW/* ch7Roles12 */ = new T1(0,_FV/* FormStructure.Chapter7.ch7Roles13 */),
_FX/* ch7Roles16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haste[\'toRoles\']()"));
}),
_FY/* ch7Roles15 */ = new T1(1,_FX/* FormStructure.Chapter7.ch7Roles16 */),
_FZ/* ch7Roles27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_G0/* ch7Roles36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_G1/* ch7Roles26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_G2/* ch7Roles59 */ = new T2(1,_G1/* FormStructure.Chapter7.ch7Roles26 */,_I/* GHC.Types.[] */),
_G3/* ch7Roles58 */ = new T2(1,_G0/* FormStructure.Chapter7.ch7Roles36 */,_G2/* FormStructure.Chapter7.ch7Roles59 */),
_G4/* ch7Roles57 */ = new T2(1,_FZ/* FormStructure.Chapter7.ch7Roles27 */,_G3/* FormStructure.Chapter7.ch7Roles58 */),
_G5/* ch7Roles61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data expert"));
}),
_G6/* ch7Roles60 */ = new T1(1,_G5/* FormStructure.Chapter7.ch7Roles61 */),
_G7/* ch7Roles56 */ = {_:0,a:_G6/* FormStructure.Chapter7.ch7Roles60 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_G4/* FormStructure.Chapter7.ch7Roles57 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_G8/* ch7Roles55 */ = new T2(3,_G7/* FormStructure.Chapter7.ch7Roles56 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_G9/* ch7Roles52 */ = new T2(1,_G0/* FormStructure.Chapter7.ch7Roles36 */,_I/* GHC.Types.[] */),
_Ga/* ch7Roles54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data consumer"));
}),
_Gb/* ch7Roles53 */ = new T1(1,_Ga/* FormStructure.Chapter7.ch7Roles54 */),
_Gc/* ch7Roles51 */ = {_:0,a:_Gb/* FormStructure.Chapter7.ch7Roles53 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_G9/* FormStructure.Chapter7.ch7Roles52 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gd/* ch7Roles50 */ = new T2(3,_Gc/* FormStructure.Chapter7.ch7Roles51 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_Ge/* ch7Roles23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_Gf/* ch7Roles22 */ = new T2(1,_Ge/* FormStructure.Chapter7.ch7Roles23 */,_I/* GHC.Types.[] */),
_Gg/* ch7Roles24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_Gh/* ch7Roles21 */ = new T2(1,_Gg/* FormStructure.Chapter7.ch7Roles24 */,_Gf/* FormStructure.Chapter7.ch7Roles22 */),
_Gi/* ch7Roles25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_Gj/* ch7Roles20 */ = new T2(1,_Gi/* FormStructure.Chapter7.ch7Roles25 */,_Gh/* FormStructure.Chapter7.ch7Roles21 */),
_Gk/* ch7Roles19 */ = new T2(1,_G1/* FormStructure.Chapter7.ch7Roles26 */,_Gj/* FormStructure.Chapter7.ch7Roles20 */),
_Gl/* ch7Roles35 */ = new T2(1,_G0/* FormStructure.Chapter7.ch7Roles36 */,_Gk/* FormStructure.Chapter7.ch7Roles19 */),
_Gm/* ch7Roles34 */ = new T2(1,_FZ/* FormStructure.Chapter7.ch7Roles27 */,_Gl/* FormStructure.Chapter7.ch7Roles35 */),
_Gn/* ch7Roles49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data curator"));
}),
_Go/* ch7Roles48 */ = new T1(1,_Gn/* FormStructure.Chapter7.ch7Roles49 */),
_Gp/* ch7Roles47 */ = {_:0,a:_Go/* FormStructure.Chapter7.ch7Roles48 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Gm/* FormStructure.Chapter7.ch7Roles34 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gq/* ch7Roles46 */ = new T2(3,_Gp/* FormStructure.Chapter7.ch7Roles47 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_Gr/* ch7Roles43 */ = new T2(1,_Gg/* FormStructure.Chapter7.ch7Roles24 */,_I/* GHC.Types.[] */),
_Gs/* ch7Roles42 */ = new T2(1,_Gi/* FormStructure.Chapter7.ch7Roles25 */,_Gr/* FormStructure.Chapter7.ch7Roles43 */),
_Gt/* ch7Roles41 */ = new T2(1,_G1/* FormStructure.Chapter7.ch7Roles26 */,_Gs/* FormStructure.Chapter7.ch7Roles42 */),
_Gu/* ch7Roles45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data custodian"));
}),
_Gv/* ch7Roles44 */ = new T1(1,_Gu/* FormStructure.Chapter7.ch7Roles45 */),
_Gw/* ch7Roles40 */ = {_:0,a:_Gv/* FormStructure.Chapter7.ch7Roles44 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Gt/* FormStructure.Chapter7.ch7Roles41 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Gx/* ch7Roles39 */ = new T2(3,_Gw/* FormStructure.Chapter7.ch7Roles40 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_Gy/* ch7Roles18 */ = new T2(1,_FZ/* FormStructure.Chapter7.ch7Roles27 */,_Gk/* FormStructure.Chapter7.ch7Roles19 */),
_Gz/* ch7Roles28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_GA/* ch7Roles17 */ = new T2(1,_Gz/* FormStructure.Chapter7.ch7Roles28 */,_Gy/* FormStructure.Chapter7.ch7Roles18 */),
_GB/* ch7Roles30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data manager"));
}),
_GC/* ch7Roles29 */ = new T1(1,_GB/* FormStructure.Chapter7.ch7Roles30 */),
_GD/* ch7Roles14 */ = {_:0,a:_GC/* FormStructure.Chapter7.ch7Roles29 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GA/* FormStructure.Chapter7.ch7Roles17 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GE/* ch7Roles11 */ = new T2(3,_GD/* FormStructure.Chapter7.ch7Roles14 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_GF/* ch7Roles10 */ = new T2(1,_GE/* FormStructure.Chapter7.ch7Roles11 */,_I/* GHC.Types.[] */),
_GG/* ch7Roles33 */ = new T2(1,_Gz/* FormStructure.Chapter7.ch7Roles28 */,_Gm/* FormStructure.Chapter7.ch7Roles34 */),
_GH/* ch7Roles38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data steward"));
}),
_GI/* ch7Roles37 */ = new T1(1,_GH/* FormStructure.Chapter7.ch7Roles38 */),
_GJ/* ch7Roles32 */ = {_:0,a:_GI/* FormStructure.Chapter7.ch7Roles37 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GG/* FormStructure.Chapter7.ch7Roles33 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GK/* ch7Roles31 */ = new T2(3,_GJ/* FormStructure.Chapter7.ch7Roles32 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_GL/* ch7Roles9 */ = new T2(1,_GK/* FormStructure.Chapter7.ch7Roles31 */,_GF/* FormStructure.Chapter7.ch7Roles10 */),
_GM/* ch7Roles8 */ = new T2(1,_Gx/* FormStructure.Chapter7.ch7Roles39 */,_GL/* FormStructure.Chapter7.ch7Roles9 */),
_GN/* ch7Roles7 */ = new T2(1,_Gq/* FormStructure.Chapter7.ch7Roles46 */,_GM/* FormStructure.Chapter7.ch7Roles8 */),
_GO/* ch7Roles6 */ = new T2(1,_Gd/* FormStructure.Chapter7.ch7Roles50 */,_GN/* FormStructure.Chapter7.ch7Roles7 */),
_GP/* ch7Roles5 */ = new T2(1,_G8/* FormStructure.Chapter7.ch7Roles55 */,_GO/* FormStructure.Chapter7.ch7Roles6 */),
_GQ/* ch7Roles64 */ = new T2(1,_Gz/* FormStructure.Chapter7.ch7Roles28 */,_I/* GHC.Types.[] */),
_GR/* ch7Roles66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data producer"));
}),
_GS/* ch7Roles65 */ = new T1(1,_GR/* FormStructure.Chapter7.ch7Roles66 */),
_GT/* ch7Roles63 */ = {_:0,a:_GS/* FormStructure.Chapter7.ch7Roles65 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_GQ/* FormStructure.Chapter7.ch7Roles64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_FY/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GU/* ch7Roles62 */ = new T2(3,_GT/* FormStructure.Chapter7.ch7Roles63 */,_FW/* FormStructure.Chapter7.ch7Roles12 */),
_GV/* ch7Roles4 */ = new T2(1,_GU/* FormStructure.Chapter7.ch7Roles62 */,_GP/* FormStructure.Chapter7.ch7Roles5 */),
_GW/* ch7Roles67 */ = 0,
_GX/* ch7Roles70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Employed roles"));
}),
_GY/* ch7Roles69 */ = new T1(1,_GX/* FormStructure.Chapter7.ch7Roles70 */),
_GZ/* ch7Roles68 */ = {_:0,a:_GY/* FormStructure.Chapter7.ch7Roles69 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_H0/* ch7Roles3 */ = new T3(7,_GZ/* FormStructure.Chapter7.ch7Roles68 */,_GW/* FormStructure.Chapter7.ch7Roles67 */,_GV/* FormStructure.Chapter7.ch7Roles4 */),
_H1/* ch7Roles1 */ = new T2(1,_H0/* FormStructure.Chapter7.ch7Roles3 */,_FU/* FormStructure.Chapter7.ch7Roles2 */),
_H2/* ch7Roles73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("7.Roles "));
}),
_H3/* ch7Roles72 */ = new T1(1,_H2/* FormStructure.Chapter7.ch7Roles73 */),
_H4/* ch7Roles71 */ = {_:0,a:_H3/* FormStructure.Chapter7.ch7Roles72 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_H5/* ch7Roles */ = new T2(6,_H4/* FormStructure.Chapter7.ch7Roles71 */,_H1/* FormStructure.Chapter7.ch7Roles1 */),
_H6/* submitForm5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save your answers."));
}),
_H7/* submitForm4 */ = new T1(1,_H6/* FormStructure.Submit.submitForm5 */),
_H8/* submitForm3 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_H7/* FormStructure.Submit.submitForm4 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_8g/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_H9/* submitForm2 */ = new T1(10,_H8/* FormStructure.Submit.submitForm3 */),
_Ha/* submitForm1 */ = new T2(1,_H9/* FormStructure.Submit.submitForm2 */,_I/* GHC.Types.[] */),
_Hb/* submitForm8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finish"));
}),
_Hc/* submitForm7 */ = new T1(1,_Hb/* FormStructure.Submit.submitForm8 */),
_Hd/* submitForm6 */ = {_:0,a:_Hc/* FormStructure.Submit.submitForm7 */,b:_89/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_He/* submitForm */ = new T2(6,_Hd/* FormStructure.Submit.submitForm6 */,_Ha/* FormStructure.Submit.submitForm1 */),
_Hf/* formItems9 */ = new T2(1,_He/* FormStructure.Submit.submitForm */,_I/* GHC.Types.[] */),
_Hg/* formItems8 */ = new T2(1,_H5/* FormStructure.Chapter7.ch7Roles */,_Hf/* FormStructure.FormStructure.formItems9 */),
_Hh/* formItems7 */ = new T2(1,_FT/* FormStructure.Chapter6.ch6DataManagement */,_Hg/* FormStructure.FormStructure.formItems8 */),
_Hi/* formItems6 */ = new T2(1,_Eg/* FormStructure.Chapter5.ch5DataAccessibility */,_Hh/* FormStructure.FormStructure.formItems7 */),
_Hj/* formItems5 */ = new T2(1,_DG/* FormStructure.Chapter4.ch4DataStorage */,_Hi/* FormStructure.FormStructure.formItems6 */),
_Hk/* formItems4 */ = new T2(1,_Cd/* FormStructure.Chapter3.ch3DataUsage */,_Hj/* FormStructure.FormStructure.formItems5 */),
_Hl/* formItems3 */ = new T2(1,_xM/* FormStructure.Chapter2.ch2DataProcessing */,_Hk/* FormStructure.FormStructure.formItems4 */),
_Hm/* formItems2 */ = new T2(1,_tu/* FormStructure.Chapter1.ch1DataProduction */,_Hl/* FormStructure.FormStructure.formItems3 */),
_Hn/* formItems1 */ = new T2(1,_ps/* FormStructure.Chapter0.ch0GeneralInformation */,_Hm/* FormStructure.FormStructure.formItems2 */),
_Ho/* prepareForm_xs */ = new T(function(){
  return new T2(1,_5O/* FormEngine.FormItem.$fShowNumbering2 */,_Ho/* FormEngine.FormItem.prepareForm_xs */);
}),
_Hp/* prepareForm1 */ = new T2(1,_Ho/* FormEngine.FormItem.prepareForm_xs */,_5O/* FormEngine.FormItem.$fShowNumbering2 */),
_Hq/* formItems */ = new T(function(){
  return E(B(_7Y/* FormEngine.FormItem.$wgo1 */(_Hn/* FormStructure.FormStructure.formItems1 */, _Hp/* FormEngine.FormItem.prepareForm1 */, _I/* GHC.Types.[] */)).b);
}),
_Hr/* $fHasChildrenFormElement_go */ = function(_Hs/*  s5Sq */, _Ht/*  s5Sr */){
  while(1){
    var _Hu/*  $fHasChildrenFormElement_go */ = B((function(_Hv/* s5Sq */, _Hw/* s5Sr */){
      var _Hx/* s5Ss */ = E(_Hv/* s5Sq */);
      if(!_Hx/* s5Ss */._){
        return E(_Hw/* s5Sr */);
      }else{
        var _Hy/*   s5Sr */ = B(_12/* GHC.Base.++ */(_Hw/* s5Sr */, new T(function(){
          var _Hz/* s5Sv */ = E(_Hx/* s5Ss */.a);
          if(!_Hz/* s5Sv */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_Hz/* s5Sv */.c);
          }
        },1)));
        _Hs/*  s5Sq */ = _Hx/* s5Ss */.b;
        _Ht/*  s5Sr */ = _Hy/*   s5Sr */;
        return __continue/* EXTERNAL */;
      }
    })(_Hs/*  s5Sq */, _Ht/*  s5Sr */));
    if(_Hu/*  $fHasChildrenFormElement_go */!=__continue/* EXTERNAL */){
      return _Hu/*  $fHasChildrenFormElement_go */;
    }
  }
},
_HA/* $fHasChildrenFormElement_$cchildren */ = function(_HB/* s5SD */){
  var _HC/* s5SE */ = E(_HB/* s5SD */);
  switch(_HC/* s5SE */._){
    case 0:
      return E(_HC/* s5SE */.b);
    case 5:
      return new F(function(){return _Hr/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_HC/* s5SE */.b, _I/* GHC.Types.[] */);});
      break;
    case 7:
      return E(_HC/* s5SE */.b);
    case 8:
      return E(_HC/* s5SE */.c);
    case 9:
      return E(_HC/* s5SE */.b);
    default:
      return __Z/* EXTERNAL */;
  }
},
_HD/* addClass2 */ = "(function (cls, jq) { jq.addClass(cls); return jq; })",
_HE/* $wa */ = function(_HF/* so16 */, _HG/* so17 */, _/* EXTERNAL */){
  var _HH/* so1h */ = eval/* EXTERNAL */(E(_HD/* FormEngine.JQuery.addClass2 */));
  return new F(function(){return E(_HH/* so1h */)(toJSStr/* EXTERNAL */(E(_HF/* so16 */)), _HG/* so17 */);});
},
_HI/* disableJq5 */ = "(function (k, v, jq) { jq.attr(k, v); return jq; })",
_HJ/* $wa6 */ = function(_HK/* so2l */, _HL/* so2m */, _HM/* so2n */, _/* EXTERNAL */){
  var _HN/* so2C */ = eval/* EXTERNAL */(E(_HI/* FormEngine.JQuery.disableJq5 */));
  return new F(function(){return E(_HN/* so2C */)(toJSStr/* EXTERNAL */(E(_HK/* so2l */)), toJSStr/* EXTERNAL */(E(_HL/* so2m */)), _HM/* so2n */);});
},
_HO/* addClassInside_f1 */ = new T(function(){
  return (function (jq) { return jq.parent(); });
}),
_HP/* addClassInside_f2 */ = new T(function(){
  return (function (jq) { return jq.last(); });
}),
_HQ/* addClassInside_f3 */ = new T(function(){
  return (function (jq) { return jq.children(); });
}),
_HR/* $wa20 */ = function(_HS/* so2U */, _HT/* so2V */, _HU/* so2W */, _/* EXTERNAL */){
  var _HV/* so31 */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_HU/* so2W */),
  _HW/* so37 */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_HV/* so31 */),
  _HX/* so3a */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_HS/* so2U */, _HT/* so2V */, _HW/* so37 */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_HX/* so3a */));});
},
_HY/* $wa24 */ = function(_HZ/* so4b */, _I0/* so4c */, _I1/* so4d */, _/* EXTERNAL */){
  var _I2/* so4i */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_I1/* so4d */),
  _I3/* so4o */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_I2/* so4i */),
  _I4/* so4r */ = B(_43/* FormEngine.JQuery.$wa2 */(_HZ/* so4b */, _I0/* so4c */, _I3/* so4o */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_I4/* so4r */));});
},
_I5/* appendT2 */ = "(function (tag, jq) { return jq.append(tag); })",
_I6/* $wa3 */ = function(_I7/* so06 */, _I8/* so07 */, _/* EXTERNAL */){
  var _I9/* so0h */ = eval/* EXTERNAL */(E(_I5/* FormEngine.JQuery.appendT2 */));
  return new F(function(){return E(_I9/* so0h */)(toJSStr/* EXTERNAL */(E(_I7/* so06 */)), _I8/* so07 */);});
},
_Ia/* setText2 */ = "(function (txt, jq) { jq.text(txt); return jq; })",
_Ib/* $wa34 */ = function(_Ic/* so6Y */, _Id/* so6Z */, _/* EXTERNAL */){
  var _Ie/* so74 */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_Id/* so6Z */),
  _If/* so7a */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_Ie/* so74 */),
  _Ig/* so7l */ = eval/* EXTERNAL */(E(_Ia/* FormEngine.JQuery.setText2 */)),
  _Ih/* so7t */ = E(_Ig/* so7l */)(toJSStr/* EXTERNAL */(E(_Ic/* so6Y */)), _If/* so7a */);
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(_Ih/* so7t */);});
},
_Ii/* appendJq_f1 */ = new T(function(){
  return (function (jq, toJq) { return toJq.append(jq); });
}),
_Ij/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<ul>"));
}),
_Ik/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("nav"));
}),
_Il/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<li>"));
}),
_Im/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_In/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<a>"));
}),
_Io/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'stripe stripe-thin\'>"));
}),
_Ip/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_Iq/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_Ir/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("class"));
}),
_Is/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inside-bordered"));
}),
_It/* onClick2 */ = "(function (ev, jq) { jq.click(ev); })",
_Iu/* onClick1 */ = function(_Iv/* snFB */, _Iw/* snFC */, _/* EXTERNAL */){
  var _Ix/* snFO */ = __createJSFunc/* EXTERNAL */(2, function(_Iy/* snFF */, _/* EXTERNAL */){
    var _Iz/* snFH */ = B(A2(E(_Iv/* snFB */),_Iy/* snFF */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _IA/* snFR */ = E(_Iw/* snFC */),
  _IB/* snFW */ = eval/* EXTERNAL */(E(_It/* FormEngine.JQuery.onClick2 */)),
  _IC/* snG4 */ = E(_IB/* snFW */)(_Ix/* snFO */, _IA/* snFR */);
  return _IA/* snFR */;
},
_ID/* paneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pane_"));
}),
_IE/* paneId */ = function(_IF/* stqr */){
  return new F(function(){return _12/* GHC.Base.++ */(_ID/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
    return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_IF/* stqr */)))).b));
  },1));});
},
_IG/* tabId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tab_"));
}),
_IH/* tabId */ = function(_II/* stqE */){
  return new F(function(){return _12/* GHC.Base.++ */(_IG/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
    return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_II/* stqE */)))).b));
  },1));});
},
_IJ/* tabName */ = function(_IK/* stoq */){
  var _IL/* stoC */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_IK/* stoq */)))).a);
  return (_IL/* stoC */._==0) ? __Z/* EXTERNAL */ : E(_IL/* stoC */.a);
},
_IM/* appearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("block"));
}),
_IN/* appearJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_IO/* eqString */ = function(_IP/* s3mQ */, _IQ/* s3mR */){
  while(1){
    var _IR/* s3mS */ = E(_IP/* s3mQ */);
    if(!_IR/* s3mS */._){
      return (E(_IQ/* s3mR */)._==0) ? true : false;
    }else{
      var _IS/* s3mY */ = E(_IQ/* s3mR */);
      if(!_IS/* s3mY */._){
        return false;
      }else{
        if(E(_IR/* s3mS */.a)!=E(_IS/* s3mY */.a)){
          return false;
        }else{
          _IP/* s3mQ */ = _IR/* s3mS */.b;
          _IQ/* s3mR */ = _IS/* s3mY */.b;
          continue;
        }
      }
    }
  }
},
_IT/* $fEqFormElement_$c== */ = function(_IU/* s5RQ */, _IV/* s5RR */){
  return new F(function(){return _IO/* GHC.Base.eqString */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_IU/* s5RQ */)))).b)), B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_IV/* s5RR */)))).b)));});
},
_IW/* removeClass2 */ = "(function (cls, jq) { jq.removeClass(cls); return jq; })",
_IX/* $wa16 */ = function(_IY/* so0B */, _IZ/* so0C */, _/* EXTERNAL */){
  var _J0/* so0M */ = eval/* EXTERNAL */(E(_IW/* FormEngine.JQuery.removeClass2 */));
  return new F(function(){return E(_J0/* so0M */)(toJSStr/* EXTERNAL */(E(_IY/* so0B */)), _IZ/* so0C */);});
},
_J1/* colorizeTabs2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("notcurrent"));
}),
_J2/* colorizeTabs3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("current"));
}),
_J3/* colorizeTabs4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_J4/* colorizeTabs1 */ = function(_J5/* suy1 */, _J6/* suy2 */, _/* EXTERNAL */){
  var _J7/* suy4 */ = function(_J8/*  suy5 */, _/* EXTERNAL */){
    while(1){
      var _J9/*  suy4 */ = B((function(_Ja/* suy5 */, _/* EXTERNAL */){
        var _Jb/* suy7 */ = E(_Ja/* suy5 */);
        if(!_Jb/* suy7 */._){
          return _0/* GHC.Tuple.() */;
        }else{
          var _Jc/* suy8 */ = _Jb/* suy7 */.a,
          _Jd/* suy9 */ = _Jb/* suy7 */.b;
          if(!B(_IT/* FormEngine.FormElement.FormElement.$fEqFormElement_$c== */(_Jc/* suy8 */, _J5/* suy1 */))){
            var _Je/* suyd */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_IH/* FormEngine.FormElement.Identifiers.tabId */(_Jc/* suy8 */));
            },1))), _/* EXTERNAL */)),
            _Jf/* suyi */ = B(_IX/* FormEngine.JQuery.$wa16 */(_J2/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_Je/* suyd */), _/* EXTERNAL */)),
            _Jg/* suyn */ = B(_HE/* FormEngine.JQuery.$wa */(_J1/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_Jf/* suyi */), _/* EXTERNAL */));
            _J8/*  suy5 */ = _Jd/* suy9 */;
            return __continue/* EXTERNAL */;
          }else{
            var _Jh/* suys */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_IH/* FormEngine.FormElement.Identifiers.tabId */(_Jc/* suy8 */));
            },1))), _/* EXTERNAL */)),
            _Ji/* suyx */ = B(_IX/* FormEngine.JQuery.$wa16 */(_J1/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_Jh/* suys */), _/* EXTERNAL */)),
            _Jj/* suyC */ = B(_HE/* FormEngine.JQuery.$wa */(_J2/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_Ji/* suyx */), _/* EXTERNAL */));
            _J8/*  suy5 */ = _Jd/* suy9 */;
            return __continue/* EXTERNAL */;
          }
        }
      })(_J8/*  suy5 */, _/* EXTERNAL */));
      if(_J9/*  suy4 */!=__continue/* EXTERNAL */){
        return _J9/*  suy4 */;
      }
    }
  };
  return new F(function(){return _J7/* suy4 */(_J6/* suy2 */, _/* EXTERNAL */);});
},
_Jk/* disappearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_Jl/* toTab2 */ = function(_Jm/* suz4 */, _/* EXTERNAL */){
  while(1){
    var _Jn/* suz6 */ = E(_Jm/* suz4 */);
    if(!_Jn/* suz6 */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _Jo/* suzb */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, E(_Jn/* suz6 */.a), _/* EXTERNAL */));
      _Jm/* suz4 */ = _Jn/* suz6 */.b;
      continue;
    }
  }
},
_Jp/* toTab3 */ = function(_Jq/* suyQ */, _/* EXTERNAL */){
  var _Jr/* suyS */ = E(_Jq/* suyQ */);
  if(!_Jr/* suyS */._){
    return _I/* GHC.Types.[] */;
  }else{
    var _Js/* suyX */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
      return B(_IE/* FormEngine.FormElement.Identifiers.paneId */(_Jr/* suyS */.a));
    },1))), _/* EXTERNAL */)),
    _Jt/* suz0 */ = B(_Jp/* FormEngine.FormElement.Tabs.toTab3 */(_Jr/* suyS */.b, _/* EXTERNAL */));
    return new T2(1,_Js/* suyX */,_Jt/* suz0 */);
  }
},
_Ju/* toTab1 */ = function(_Jv/* suze */, _Jw/* suzf */, _/* EXTERNAL */){
  var _Jx/* suzj */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
    return B(_IE/* FormEngine.FormElement.Identifiers.paneId */(_Jv/* suze */));
  },1))), _/* EXTERNAL */)),
  _Jy/* suzm */ = B(_Jp/* FormEngine.FormElement.Tabs.toTab3 */(_Jw/* suzf */, _/* EXTERNAL */)),
  _Jz/* suzp */ = B(_J4/* FormEngine.FormElement.Tabs.colorizeTabs1 */(_Jv/* suze */, _Jw/* suzf */, _/* EXTERNAL */)),
  _JA/* suzs */ = B(_Jl/* FormEngine.FormElement.Tabs.toTab2 */(_Jy/* suzm */, _/* EXTERNAL */)),
  _JB/* suzx */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _IM/* FormEngine.JQuery.appearJq2 */, E(_Jx/* suzj */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_JC/* $wa */ = function(_JD/* suzA */, _JE/* suzB */, _JF/* suzC */, _/* EXTERNAL */){
  var _JG/* suzE */ = B(_I6/* FormEngine.JQuery.$wa3 */(_Ij/* FormEngine.FormElement.Tabs.lvl */, _JF/* suzC */, _/* EXTERNAL */)),
  _JH/* suzJ */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
  _JI/* suzM */ = _JH/* suzJ */(E(_JG/* suzE */)),
  _JJ/* suzP */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
  _JK/* suzS */ = _JJ/* suzP */(_JI/* suzM */),
  _JL/* suzV */ = B(_HE/* FormEngine.JQuery.$wa */(_Ik/* FormEngine.FormElement.Tabs.lvl1 */, _JK/* suzS */, _/* EXTERNAL */)),
  _JM/* suzY */ = function(_/* EXTERNAL */, _JN/* suA0 */){
    var _JO/* suA6 */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_JN/* suA0 */)),
    _JP/* suA9 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_Io/* FormEngine.FormElement.Tabs.lvl5 */, _JO/* suA6 */, _/* EXTERNAL */)),
    _JQ/* suAc */ = E(_JD/* suzA */);
    if(!_JQ/* suAc */._){
      return _JP/* suA9 */;
    }else{
      var _JR/* suAf */ = E(_JE/* suzB */);
      if(!_JR/* suAf */._){
        return _JP/* suA9 */;
      }else{
        var _JS/* suAi */ = B(A1(_JR/* suAf */.a,_/* EXTERNAL */)),
        _JT/* suAp */ = E(_Ii/* FormEngine.JQuery.appendJq_f1 */),
        _JU/* suAs */ = _JT/* suAp */(E(_JS/* suAi */), E(_JP/* suA9 */)),
        _JV/* suAw */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Im/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
          return B(_IE/* FormEngine.FormElement.Identifiers.paneId */(_JQ/* suAc */.a));
        },1), _JU/* suAs */, _/* EXTERNAL */)),
        _JW/* suAB */ = B(_HY/* FormEngine.JQuery.$wa24 */(_Ip/* FormEngine.FormElement.Tabs.lvl6 */, _Iq/* FormEngine.FormElement.Tabs.lvl7 */, E(_JV/* suAw */), _/* EXTERNAL */)),
        _JX/* suAG */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Ir/* FormEngine.FormElement.Tabs.lvl8 */, _Is/* FormEngine.FormElement.Tabs.lvl9 */, E(_JW/* suAB */), _/* EXTERNAL */)),
        _JY/* suAJ */ = function(_JZ/*  suAK */, _K0/*  suAL */, _K1/*  suAM */, _/* EXTERNAL */){
          while(1){
            var _K2/*  suAJ */ = B((function(_K3/* suAK */, _K4/* suAL */, _K5/* suAM */, _/* EXTERNAL */){
              var _K6/* suAO */ = E(_K3/* suAK */);
              if(!_K6/* suAO */._){
                return _K5/* suAM */;
              }else{
                var _K7/* suAR */ = E(_K4/* suAL */);
                if(!_K7/* suAR */._){
                  return _K5/* suAM */;
                }else{
                  var _K8/* suAU */ = B(A1(_K7/* suAR */.a,_/* EXTERNAL */)),
                  _K9/* suB2 */ = _JT/* suAp */(E(_K8/* suAU */), E(_K5/* suAM */)),
                  _Ka/* suB6 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Im/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
                    return B(_IE/* FormEngine.FormElement.Identifiers.paneId */(_K6/* suAO */.a));
                  },1), _K9/* suB2 */, _/* EXTERNAL */)),
                  _Kb/* suBb */ = B(_HY/* FormEngine.JQuery.$wa24 */(_Ip/* FormEngine.FormElement.Tabs.lvl6 */, _Iq/* FormEngine.FormElement.Tabs.lvl7 */, E(_Ka/* suB6 */), _/* EXTERNAL */)),
                  _Kc/* suBg */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Ir/* FormEngine.FormElement.Tabs.lvl8 */, _Is/* FormEngine.FormElement.Tabs.lvl9 */, E(_Kb/* suBb */), _/* EXTERNAL */));
                  _JZ/*  suAK */ = _K6/* suAO */.b;
                  _K0/*  suAL */ = _K7/* suAR */.b;
                  _K1/*  suAM */ = _Kc/* suBg */;
                  return __continue/* EXTERNAL */;
                }
              }
            })(_JZ/*  suAK */, _K0/*  suAL */, _K1/*  suAM */, _/* EXTERNAL */));
            if(_K2/*  suAJ */!=__continue/* EXTERNAL */){
              return _K2/*  suAJ */;
            }
          }
        };
        return new F(function(){return _JY/* suAJ */(_JQ/* suAc */.b, _JR/* suAf */.b, _JX/* suAG */, _/* EXTERNAL */);});
      }
    }
  },
  _Kd/* suBj */ = E(_JD/* suzA */);
  if(!_Kd/* suBj */._){
    return new F(function(){return _JM/* suzY */(_/* EXTERNAL */, _JL/* suzV */);});
  }else{
    var _Ke/* suBk */ = _Kd/* suBj */.a,
    _Kf/* suBo */ = B(_I6/* FormEngine.JQuery.$wa3 */(_Il/* FormEngine.FormElement.Tabs.lvl2 */, E(_JL/* suzV */), _/* EXTERNAL */)),
    _Kg/* suBu */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Im/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
      return B(_IH/* FormEngine.FormElement.Identifiers.tabId */(_Ke/* suBk */));
    },1), E(_Kf/* suBo */), _/* EXTERNAL */)),
    _Kh/* suBA */ = _JH/* suzJ */(E(_Kg/* suBu */)),
    _Ki/* suBE */ = _JJ/* suzP */(_Kh/* suBA */),
    _Kj/* suBH */ = B(_I6/* FormEngine.JQuery.$wa3 */(_In/* FormEngine.FormElement.Tabs.lvl4 */, _Ki/* suBE */, _/* EXTERNAL */)),
    _Kk/* suBN */ = B(_Iu/* FormEngine.JQuery.onClick1 */(function(_Kl/* suBK */, _/* EXTERNAL */){
      return new F(function(){return _Ju/* FormEngine.FormElement.Tabs.toTab1 */(_Ke/* suBk */, _Kd/* suBj */, _/* EXTERNAL */);});
    }, _Kj/* suBH */, _/* EXTERNAL */)),
    _Km/* suBT */ = B(_Ib/* FormEngine.JQuery.$wa34 */(new T(function(){
      return B(_IJ/* FormEngine.FormElement.Identifiers.tabName */(_Ke/* suBk */));
    },1), E(_Kk/* suBN */), _/* EXTERNAL */)),
    _Kn/* suBY */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
    _Ko/* suC1 */ = _Kn/* suBY */(E(_Km/* suBT */)),
    _Kp/* suC4 */ = function(_Kq/*  suC5 */, _Kr/*  suC6 */, _Ks/*  sutS */, _/* EXTERNAL */){
      while(1){
        var _Kt/*  suC4 */ = B((function(_Ku/* suC5 */, _Kv/* suC6 */, _Kw/* sutS */, _/* EXTERNAL */){
          var _Kx/* suC8 */ = E(_Ku/* suC5 */);
          if(!_Kx/* suC8 */._){
            return _Kv/* suC6 */;
          }else{
            var _Ky/* suCa */ = _Kx/* suC8 */.a,
            _Kz/* suCc */ = B(_I6/* FormEngine.JQuery.$wa3 */(_Il/* FormEngine.FormElement.Tabs.lvl2 */, _Kv/* suC6 */, _/* EXTERNAL */)),
            _KA/* suCi */ = B(_HR/* FormEngine.JQuery.$wa20 */(_Im/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
              return B(_IH/* FormEngine.FormElement.Identifiers.tabId */(_Ky/* suCa */));
            },1), E(_Kz/* suCc */), _/* EXTERNAL */)),
            _KB/* suCo */ = _JH/* suzJ */(E(_KA/* suCi */)),
            _KC/* suCs */ = _JJ/* suzP */(_KB/* suCo */),
            _KD/* suCv */ = B(_I6/* FormEngine.JQuery.$wa3 */(_In/* FormEngine.FormElement.Tabs.lvl4 */, _KC/* suCs */, _/* EXTERNAL */)),
            _KE/* suCB */ = B(_Iu/* FormEngine.JQuery.onClick1 */(function(_KF/* suCy */, _/* EXTERNAL */){
              return new F(function(){return _Ju/* FormEngine.FormElement.Tabs.toTab1 */(_Ky/* suCa */, _Kd/* suBj */, _/* EXTERNAL */);});
            }, _KD/* suCv */, _/* EXTERNAL */)),
            _KG/* suCH */ = B(_Ib/* FormEngine.JQuery.$wa34 */(new T(function(){
              return B(_IJ/* FormEngine.FormElement.Identifiers.tabName */(_Ky/* suCa */));
            },1), E(_KE/* suCB */), _/* EXTERNAL */)),
            _KH/* suCN */ = _Kn/* suBY */(E(_KG/* suCH */)),
            _KI/*   sutS */ = _/* EXTERNAL */;
            _Kq/*  suC5 */ = _Kx/* suC8 */.b;
            _Kr/*  suC6 */ = _KH/* suCN */;
            _Ks/*  sutS */ = _KI/*   sutS */;
            return __continue/* EXTERNAL */;
          }
        })(_Kq/*  suC5 */, _Kr/*  suC6 */, _Ks/*  sutS */, _/* EXTERNAL */));
        if(_Kt/*  suC4 */!=__continue/* EXTERNAL */){
          return _Kt/*  suC4 */;
        }
      }
    },
    _KJ/* suCQ */ = B(_Kp/* suC4 */(_Kd/* suBj */.b, _Ko/* suC1 */, _/* EXTERNAL */, _/* EXTERNAL */));
    return new F(function(){return _JM/* suzY */(_/* EXTERNAL */, _KJ/* suCQ */);});
  }
},
_KK/* mouseleave2 */ = "(function (jq) { jq.mouseleave(); })",
_KL/* $wa14 */ = function(_KM/* snHi */, _/* EXTERNAL */){
  var _KN/* snHn */ = eval/* EXTERNAL */(E(_KK/* FormEngine.JQuery.mouseleave2 */)),
  _KO/* snHv */ = E(_KN/* snHn */)(_KM/* snHi */);
  return _KM/* snHi */;
},
_KP/* setHtml2 */ = "(function (html, jq) { jq.html(html); return jq; })",
_KQ/* $wa26 */ = function(_KR/* so5h */, _KS/* so5i */, _/* EXTERNAL */){
  var _KT/* so5s */ = eval/* EXTERNAL */(E(_KP/* FormEngine.JQuery.setHtml2 */));
  return new F(function(){return E(_KT/* so5s */)(toJSStr/* EXTERNAL */(E(_KR/* so5h */)), _KS/* so5i */);});
},
_KU/* onLoad2 */ = "(function (ev, jq) { jq[0].addEventListener(\'load\', ev); })",
_KV/* onLoad1 */ = function(_KW/* snBg */, _KX/* snBh */, _/* EXTERNAL */){
  var _KY/* snBt */ = __createJSFunc/* EXTERNAL */(2, function(_KZ/* snBk */, _/* EXTERNAL */){
    var _L0/* snBm */ = B(A2(E(_KW/* snBg */),_KZ/* snBk */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _L1/* snBw */ = E(_KX/* snBh */),
  _L2/* snBB */ = eval/* EXTERNAL */(E(_KU/* FormEngine.JQuery.onLoad2 */)),
  _L3/* snBJ */ = E(_L2/* snBB */)(_KY/* snBt */, _L1/* snBw */);
  return _L1/* snBw */;
},
_L4/* $wa29 */ = function(_L5/* snRd */, _L6/* snRe */, _/* EXTERNAL */){
  var _L7/* snRj */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_L6/* snRe */),
  _L8/* snRp */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_L7/* snRj */),
  _L9/* snRt */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_L5/* snRd */, _L8/* snRp */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_L9/* snRt */));});
},
_La/* click2 */ = "(function (jq) { jq.click(); })",
_Lb/* $wa5 */ = function(_Lc/* snIs */, _/* EXTERNAL */){
  var _Ld/* snIx */ = eval/* EXTERNAL */(E(_La/* FormEngine.JQuery.click2 */)),
  _Le/* snIF */ = E(_Ld/* snIx */)(_Lc/* snIs */);
  return _Lc/* snIs */;
},
_Lf/* aboutTab4 */ = 0,
_Lg/* aboutTab6 */ = 1000,
_Lh/* aboutTab5 */ = new T2(1,_Lg/* Form.aboutTab6 */,_I/* GHC.Types.[] */),
_Li/* aboutTab3 */ = new T2(1,_Lh/* Form.aboutTab5 */,_Lf/* Form.aboutTab4 */),
_Lj/* aboutTab8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("About"));
}),
_Lk/* aboutTab7 */ = new T1(1,_Lj/* Form.aboutTab8 */),
_Ll/* aboutTab2 */ = {_:0,a:_Lk/* Form.aboutTab7 */,b:_Li/* Form.aboutTab3 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Lm/* aboutTab1 */ = new T2(6,_Ll/* Form.aboutTab2 */,_I/* GHC.Types.[] */),
_Ln/* aboutTab */ = new T3(0,_Lm/* Form.aboutTab1 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_Lo/* aboutTabPaneJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("  <div>    <p>      This questionnaire aims to collect managerial information about the bioinformatics data space.    </p>    <p>      <strong>Only data where the respondent is the owner are subject of the questionnaires</strong>, i.e. not data produced as a service.    </p>    <p>      Its completion should take no more than 15 minutes. If you do not know exact answer, provide your best qualified guess.    </p>    <p>      For questions please contact <a href=\'mailto:robert.pergl@fit.cvut.cz\'>robert.pergl@fit.cvut.cz</a>.    </p>    <br>    <p style=\'font-size: 90%; font-style: italic;\'>      Version of this questionnaire: v2.0    </p>  </div> "));
}),
_Lp/* aboutTabPaneJq1 */ = function(_/* EXTERNAL */){
  return new F(function(){return _50/* FormEngine.JQuery.select1 */(_Lo/* Form.aboutTabPaneJq2 */, _/* EXTERNAL */);});
},
_Lq/* descSubpaneParagraphId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane-text"));
}),
_Lr/* descSubpaneParagraphId */ = function(_Ls/* stqR */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_Ls/* stqR */)))))).b)), _Lq/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */);});
},
_Lt/* diagramId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("diagram_"));
}),
_Lu/* diagramId */ = function(_Lv/* stqd */){
  return new F(function(){return _12/* GHC.Base.++ */(_Lt/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
    return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(B(_4n/* FormEngine.FormElement.FormElement.elemChapter */(_Lv/* stqd */)))))).b));
  },1));});
},
_Lw/* $fEqOption_$c== */ = function(_Lx/* s7De */, _Ly/* s7Df */){
  var _Lz/* s7Dg */ = E(_Lx/* s7De */);
  if(!_Lz/* s7Dg */._){
    var _LA/* s7Dh */ = _Lz/* s7Dg */.a,
    _LB/* s7Di */ = E(_Ly/* s7Df */);
    if(!_LB/* s7Di */._){
      return new F(function(){return _IO/* GHC.Base.eqString */(_LA/* s7Dh */, _LB/* s7Di */.a);});
    }else{
      return new F(function(){return _IO/* GHC.Base.eqString */(_LA/* s7Dh */, _LB/* s7Di */.b);});
    }
  }else{
    var _LC/* s7Do */ = _Lz/* s7Dg */.b,
    _LD/* s7Dq */ = E(_Ly/* s7Df */);
    if(!_LD/* s7Dq */._){
      return new F(function(){return _IO/* GHC.Base.eqString */(_LC/* s7Do */, _LD/* s7Dq */.a);});
    }else{
      return new F(function(){return _IO/* GHC.Base.eqString */(_LC/* s7Do */, _LD/* s7Dq */.b);});
    }
  }
},
_LE/* $fShowFormElement1 */ = function(_LF/* s5SV */, _LG/* s5SW */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_LH/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_LF/* s5SV */)), _LG/* s5SW */);});
},
_LI/* $fShowMaybe1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just "));
}),
_LJ/* $fShowMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_LK/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SubmitButtonElem id="));
}),
_LL/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SaveButtonElem id="));
}),
_LM/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumberElem id="));
}),
_LN/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EmailElem id="));
}),
_LO/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TextElem id="));
}),
_LP/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("StringElem id="));
}),
_LQ/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChapterElem id="));
}),
_LR/* shows5 */ = 34,
_LS/* lvl15 */ = new T2(1,_LR/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_LT/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElem id="));
}),
_LU/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" children: "));
}),
_LV/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OptionalGroupElem id="));
}),
_LW/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SimpleGroupElem id="));
}),
_LX/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" value="));
}),
_LY/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ListElem id="));
}),
_LZ/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChoiceElem id="));
}),
_M0/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" unit="));
}),
_M1/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_M2/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_M3/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_M4/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_M5/* asciiTab32 */ = new T2(1,_M4/* GHC.Show.asciiTab33 */,_I/* GHC.Types.[] */),
_M6/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_M7/* asciiTab31 */ = new T2(1,_M6/* GHC.Show.asciiTab34 */,_M5/* GHC.Show.asciiTab32 */),
_M8/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_M9/* asciiTab30 */ = new T2(1,_M8/* GHC.Show.asciiTab35 */,_M7/* GHC.Show.asciiTab31 */),
_Ma/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_Mb/* asciiTab29 */ = new T2(1,_Ma/* GHC.Show.asciiTab36 */,_M9/* GHC.Show.asciiTab30 */),
_Mc/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_Md/* asciiTab28 */ = new T2(1,_Mc/* GHC.Show.asciiTab37 */,_Mb/* GHC.Show.asciiTab29 */),
_Me/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_Mf/* asciiTab27 */ = new T2(1,_Me/* GHC.Show.asciiTab38 */,_Md/* GHC.Show.asciiTab28 */),
_Mg/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_Mh/* asciiTab26 */ = new T2(1,_Mg/* GHC.Show.asciiTab39 */,_Mf/* GHC.Show.asciiTab27 */),
_Mi/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_Mj/* asciiTab25 */ = new T2(1,_Mi/* GHC.Show.asciiTab40 */,_Mh/* GHC.Show.asciiTab26 */),
_Mk/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_Ml/* asciiTab24 */ = new T2(1,_Mk/* GHC.Show.asciiTab41 */,_Mj/* GHC.Show.asciiTab25 */),
_Mm/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_Mn/* asciiTab23 */ = new T2(1,_Mm/* GHC.Show.asciiTab42 */,_Ml/* GHC.Show.asciiTab24 */),
_Mo/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_Mp/* asciiTab22 */ = new T2(1,_Mo/* GHC.Show.asciiTab43 */,_Mn/* GHC.Show.asciiTab23 */),
_Mq/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_Mr/* asciiTab21 */ = new T2(1,_Mq/* GHC.Show.asciiTab44 */,_Mp/* GHC.Show.asciiTab22 */),
_Ms/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_Mt/* asciiTab20 */ = new T2(1,_Ms/* GHC.Show.asciiTab45 */,_Mr/* GHC.Show.asciiTab21 */),
_Mu/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_Mv/* asciiTab19 */ = new T2(1,_Mu/* GHC.Show.asciiTab46 */,_Mt/* GHC.Show.asciiTab20 */),
_Mw/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_Mx/* asciiTab18 */ = new T2(1,_Mw/* GHC.Show.asciiTab47 */,_Mv/* GHC.Show.asciiTab19 */),
_My/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_Mz/* asciiTab17 */ = new T2(1,_My/* GHC.Show.asciiTab48 */,_Mx/* GHC.Show.asciiTab18 */),
_MA/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_MB/* asciiTab16 */ = new T2(1,_MA/* GHC.Show.asciiTab49 */,_Mz/* GHC.Show.asciiTab17 */),
_MC/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_MD/* asciiTab15 */ = new T2(1,_MC/* GHC.Show.asciiTab50 */,_MB/* GHC.Show.asciiTab16 */),
_ME/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_MF/* asciiTab14 */ = new T2(1,_ME/* GHC.Show.asciiTab51 */,_MD/* GHC.Show.asciiTab15 */),
_MG/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_MH/* asciiTab13 */ = new T2(1,_MG/* GHC.Show.asciiTab52 */,_MF/* GHC.Show.asciiTab14 */),
_MI/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_MJ/* asciiTab12 */ = new T2(1,_MI/* GHC.Show.asciiTab53 */,_MH/* GHC.Show.asciiTab13 */),
_MK/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_ML/* asciiTab11 */ = new T2(1,_MK/* GHC.Show.asciiTab54 */,_MJ/* GHC.Show.asciiTab12 */),
_MM/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_MN/* asciiTab10 */ = new T2(1,_MM/* GHC.Show.asciiTab55 */,_ML/* GHC.Show.asciiTab11 */),
_MO/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_MP/* asciiTab9 */ = new T2(1,_MO/* GHC.Show.asciiTab56 */,_MN/* GHC.Show.asciiTab10 */),
_MQ/* asciiTab8 */ = new T2(1,_M3/* GHC.Show.asciiTab57 */,_MP/* GHC.Show.asciiTab9 */),
_MR/* asciiTab7 */ = new T2(1,_M2/* GHC.Show.asciiTab58 */,_MQ/* GHC.Show.asciiTab8 */),
_MS/* asciiTab6 */ = new T2(1,_M1/* GHC.Show.asciiTab59 */,_MR/* GHC.Show.asciiTab7 */),
_MT/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_MU/* asciiTab5 */ = new T2(1,_MT/* GHC.Show.asciiTab60 */,_MS/* GHC.Show.asciiTab6 */),
_MV/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_MW/* asciiTab4 */ = new T2(1,_MV/* GHC.Show.asciiTab61 */,_MU/* GHC.Show.asciiTab5 */),
_MX/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_MY/* asciiTab3 */ = new T2(1,_MX/* GHC.Show.asciiTab62 */,_MW/* GHC.Show.asciiTab4 */),
_MZ/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_N0/* asciiTab2 */ = new T2(1,_MZ/* GHC.Show.asciiTab63 */,_MY/* GHC.Show.asciiTab3 */),
_N1/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_N2/* asciiTab1 */ = new T2(1,_N1/* GHC.Show.asciiTab64 */,_N0/* GHC.Show.asciiTab2 */),
_N3/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_N4/* asciiTab */ = new T2(1,_N3/* GHC.Show.asciiTab65 */,_N2/* GHC.Show.asciiTab1 */),
_N5/* lvl */ = 92,
_N6/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_N7/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_N8/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_N9/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_Na/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_Nb/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_Nc/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_Nd/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_Ne/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_Nf/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_Ng/* $wshowLitChar */ = function(_Nh/* sfeh */, _Ni/* sfei */){
  if(_Nh/* sfeh */<=127){
    var _Nj/* sfel */ = E(_Nh/* sfeh */);
    switch(_Nj/* sfel */){
      case 92:
        return new F(function(){return _12/* GHC.Base.++ */(_N8/* GHC.Show.lvl2 */, _Ni/* sfei */);});
        break;
      case 127:
        return new F(function(){return _12/* GHC.Base.++ */(_N6/* GHC.Show.lvl1 */, _Ni/* sfei */);});
        break;
      default:
        if(_Nj/* sfel */<32){
          var _Nk/* sfeo */ = E(_Nj/* sfel */);
          switch(_Nk/* sfeo */){
            case 7:
              return new F(function(){return _12/* GHC.Base.++ */(_N7/* GHC.Show.lvl10 */, _Ni/* sfei */);});
              break;
            case 8:
              return new F(function(){return _12/* GHC.Base.++ */(_Nf/* GHC.Show.lvl9 */, _Ni/* sfei */);});
              break;
            case 9:
              return new F(function(){return _12/* GHC.Base.++ */(_Ne/* GHC.Show.lvl8 */, _Ni/* sfei */);});
              break;
            case 10:
              return new F(function(){return _12/* GHC.Base.++ */(_Nd/* GHC.Show.lvl7 */, _Ni/* sfei */);});
              break;
            case 11:
              return new F(function(){return _12/* GHC.Base.++ */(_Nc/* GHC.Show.lvl6 */, _Ni/* sfei */);});
              break;
            case 12:
              return new F(function(){return _12/* GHC.Base.++ */(_Nb/* GHC.Show.lvl5 */, _Ni/* sfei */);});
              break;
            case 13:
              return new F(function(){return _12/* GHC.Base.++ */(_Na/* GHC.Show.lvl4 */, _Ni/* sfei */);});
              break;
            case 14:
              return new F(function(){return _12/* GHC.Base.++ */(_N9/* GHC.Show.lvl3 */, new T(function(){
                var _Nl/* sfes */ = E(_Ni/* sfei */);
                if(!_Nl/* sfes */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_Nl/* sfes */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _Nl/* sfes */));
                  }else{
                    return E(_Nl/* sfes */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _12/* GHC.Base.++ */(new T2(1,_N5/* GHC.Show.lvl */,new T(function(){
                return B(_6V/* GHC.List.$w!! */(_N4/* GHC.Show.asciiTab */, _Nk/* sfeo */));
              })), _Ni/* sfei */);});
          }
        }else{
          return new T2(1,_Nj/* sfel */,_Ni/* sfei */);
        }
    }
  }else{
    var _Nm/* sfeR */ = new T(function(){
      var _Nn/* sfeC */ = jsShowI/* EXTERNAL */(_Nh/* sfeh */);
      return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_Nn/* sfeC */), new T(function(){
        var _No/* sfeH */ = E(_Ni/* sfei */);
        if(!_No/* sfeH */._){
          return __Z/* EXTERNAL */;
        }else{
          var _Np/* sfeK */ = E(_No/* sfeH */.a);
          if(_Np/* sfeK */<48){
            return E(_No/* sfeH */);
          }else{
            if(_Np/* sfeK */>57){
              return E(_No/* sfeH */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _No/* sfeH */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_N5/* GHC.Show.lvl */,_Nm/* sfeR */);
  }
},
_Nq/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_Nr/* showLitString */ = function(_Ns/* sfeW */, _Nt/* sfeX */){
  var _Nu/* sfeY */ = E(_Ns/* sfeW */);
  if(!_Nu/* sfeY */._){
    return E(_Nt/* sfeX */);
  }else{
    var _Nv/* sff0 */ = _Nu/* sfeY */.b,
    _Nw/* sff3 */ = E(_Nu/* sfeY */.a);
    if(_Nw/* sff3 */==34){
      return new F(function(){return _12/* GHC.Base.++ */(_Nq/* GHC.Show.lvl11 */, new T(function(){
        return B(_Nr/* GHC.Show.showLitString */(_Nv/* sff0 */, _Nt/* sfeX */));
      },1));});
    }else{
      return new F(function(){return _Ng/* GHC.Show.$wshowLitChar */(_Nw/* sff3 */, new T(function(){
        return B(_Nr/* GHC.Show.showLitString */(_Nv/* sff0 */, _Nt/* sfeX */));
      }));});
    }
  }
},
_LH/* $fShowFormElement_$cshow */ = function(_Nx/* s5SY */){
  var _Ny/* s5SZ */ = E(_Nx/* s5SY */);
  switch(_Ny/* s5SZ */._){
    case 0:
      var _Nz/* s5Tg */ = new T(function(){
        var _NA/* s5Tf */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_LU/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_LE/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _Ny/* s5SZ */.b, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), _NA/* s5Tf */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LQ/* FormEngine.FormElement.FormElement.lvl14 */, _Nz/* s5Tg */);});
      break;
    case 1:
      var _NB/* s5Tw */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_LX/* FormEngine.FormElement.FormElement.lvl6 */, _Ny/* s5SZ */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LP/* FormEngine.FormElement.FormElement.lvl13 */, _NB/* s5Tw */);});
      break;
    case 2:
      var _NC/* s5TM */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_LX/* FormEngine.FormElement.FormElement.lvl6 */, _Ny/* s5SZ */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LO/* FormEngine.FormElement.FormElement.lvl12 */, _NC/* s5TM */);});
      break;
    case 3:
      var _ND/* s5U2 */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_LX/* FormEngine.FormElement.FormElement.lvl6 */, _Ny/* s5SZ */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LN/* FormEngine.FormElement.FormElement.lvl11 */, _ND/* s5U2 */);});
      break;
    case 4:
      var _NE/* s5Uw */ = new T(function(){
        var _NF/* s5Uv */ = new T(function(){
          var _NG/* s5Uu */ = new T(function(){
            var _NH/* s5Ui */ = new T(function(){
              var _NI/* s5Un */ = new T(function(){
                var _NJ/* s5Uj */ = E(_Ny/* s5SZ */.c);
                if(!_NJ/* s5Uj */._){
                  return E(_LJ/* GHC.Show.$fShowMaybe3 */);
                }else{
                  return B(_12/* GHC.Base.++ */(_LI/* GHC.Show.$fShowMaybe1 */, new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
                    return B(_Nr/* GHC.Show.showLitString */(_NJ/* s5Uj */.a, _LS/* FormEngine.FormElement.FormElement.lvl15 */));
                  }))));
                }
              },1);
              return B(_12/* GHC.Base.++ */(_M0/* FormEngine.FormElement.FormElement.lvl9 */, _NI/* s5Un */));
            }),
            _NK/* s5Uo */ = E(_Ny/* s5SZ */.b);
            if(!_NK/* s5Uo */._){
              return B(_12/* GHC.Base.++ */(_LJ/* GHC.Show.$fShowMaybe3 */, _NH/* s5Ui */));
            }else{
              return B(_12/* GHC.Base.++ */(_LI/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(11, E(_NK/* s5Uo */.a), _I/* GHC.Types.[] */)), _NH/* s5Ui */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_LX/* FormEngine.FormElement.FormElement.lvl6 */, _NG/* s5Uu */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), _NF/* s5Uv */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LM/* FormEngine.FormElement.FormElement.lvl10 */, _NE/* s5Uw */);});
      break;
    case 5:
      return new F(function(){return _12/* GHC.Base.++ */(_LZ/* FormEngine.FormElement.FormElement.lvl8 */, new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b));
      },1));});
      break;
    case 6:
      var _NL/* s5V5 */ = new T(function(){
        var _NM/* s5V4 */ = new T(function(){
          var _NN/* s5V3 */ = new T(function(){
            var _NO/* s5UZ */ = E(_Ny/* s5SZ */.b);
            if(!_NO/* s5UZ */._){
              return E(_LJ/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_12/* GHC.Base.++ */(_LI/* GHC.Show.$fShowMaybe1 */, new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
                return B(_Nr/* GHC.Show.showLitString */(_NO/* s5UZ */.a, _LS/* FormEngine.FormElement.FormElement.lvl15 */));
              }))));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_LX/* FormEngine.FormElement.FormElement.lvl6 */, _NN/* s5V3 */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), _NM/* s5V4 */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LY/* FormEngine.FormElement.FormElement.lvl7 */, _NL/* s5V5 */);});
      break;
    case 7:
      var _NP/* s5Vm */ = new T(function(){
        var _NQ/* s5Vl */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_LU/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_LE/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _Ny/* s5SZ */.b, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), _NQ/* s5Vl */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LW/* FormEngine.FormElement.FormElement.lvl5 */, _NP/* s5Vm */);});
      break;
    case 8:
      var _NR/* s5VE */ = new T(function(){
        var _NS/* s5VD */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_LU/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_LE/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _Ny/* s5SZ */.c, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b)), _NS/* s5VD */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_LV/* FormEngine.FormElement.FormElement.lvl4 */, _NR/* s5VE */);});
      break;
    case 9:
      return new F(function(){return _12/* GHC.Base.++ */(_LT/* FormEngine.FormElement.FormElement.lvl2 */, new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b));
      },1));});
      break;
    case 10:
      return new F(function(){return _12/* GHC.Base.++ */(_LL/* FormEngine.FormElement.FormElement.lvl1 */, new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b));
      },1));});
      break;
    default:
      return new F(function(){return _12/* GHC.Base.++ */(_LK/* FormEngine.FormElement.FormElement.lvl */, new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_Ny/* s5SZ */.a)).b));
      },1));});
  }
},
_NT/* lvl54 */ = new T2(1,_LR/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_NU/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IntValueRule (Int -> Bool)"));
}),
_NV/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ReadOnlyRule"));
}),
_NW/* shows_$cshowList */ = function(_NX/* sff6 */, _NY/* sff7 */){
  return new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
    return B(_Nr/* GHC.Show.showLitString */(_NX/* sff6 */, new T2(1,_LR/* GHC.Show.shows5 */,_NY/* sff7 */)));
  }));
},
_NZ/* $fShowFormRule_$cshow */ = function(_O0/* s7Cw */){
  var _O1/* s7Cx */ = E(_O0/* s7Cw */);
  switch(_O1/* s7Cx */._){
    case 0:
      var _O2/* s7CE */ = new T(function(){
        var _O3/* s7CD */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
            return B(_Nr/* GHC.Show.showLitString */(_O1/* s7Cx */.b, _NT/* FormEngine.FormItem.lvl54 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_NW/* GHC.Show.shows_$cshowList */, _O1/* s7Cx */.a, _I/* GHC.Types.[] */)), _O3/* s7CD */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumRule @ ", _O2/* s7CE */);});
      break;
    case 1:
      var _O4/* s7CL */ = new T(function(){
        var _O5/* s7CK */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
            return B(_Nr/* GHC.Show.showLitString */(_O1/* s7Cx */.b, _NT/* FormEngine.FormItem.lvl54 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_NW/* GHC.Show.shows_$cshowList */, _O1/* s7Cx */.a, _I/* GHC.Types.[] */)), _O5/* s7CK */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumTBsRule @ ", _O4/* s7CL */);});
      break;
    case 2:
      var _O6/* s7CT */ = new T(function(){
        var _O7/* s7CS */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
            return B(_Nr/* GHC.Show.showLitString */(_O1/* s7Cx */.b, _NT/* FormEngine.FormItem.lvl54 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
          return B(_Nr/* GHC.Show.showLitString */(_O1/* s7Cx */.a, _NT/* FormEngine.FormItem.lvl54 */));
        })), _O7/* s7CS */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("CopyValueRule @ ", _O6/* s7CT */);});
      break;
    case 3:
      return E(_NV/* FormEngine.FormItem.lvl7 */);
    default:
      return E(_NU/* FormEngine.FormItem.lvl6 */);
  }
},
_O8/* identity2element' */ = function(_O9/* s6IT */, _Oa/* s6IU */){
  var _Ob/* s6IV */ = E(_Oa/* s6IU */);
  if(!_Ob/* s6IV */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Oc/* s6IW */ = _Ob/* s6IV */.a,
    _Od/* s6J9 */ = function(_Oe/* s6Ja */){
      var _Of/* s6Jc */ = B(_O8/* FormEngine.FormElement.Updating.identity2element' */(_O9/* s6IT */, B(_HA/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_Oc/* s6IW */))));
      if(!_Of/* s6Jc */._){
        return new F(function(){return _O8/* FormEngine.FormElement.Updating.identity2element' */(_O9/* s6IT */, _Ob/* s6IV */.b);});
      }else{
        return E(_Of/* s6Jc */);
      }
    },
    _Og/* s6Je */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_Oc/* s6IW */)))).c);
    if(!_Og/* s6Je */._){
      if(!B(_IO/* GHC.Base.eqString */(_I/* GHC.Types.[] */, _O9/* s6IT */))){
        return new F(function(){return _Od/* s6J9 */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Oc/* s6IW */);
      }
    }else{
      if(!B(_IO/* GHC.Base.eqString */(_Og/* s6Je */.a, _O9/* s6IT */))){
        return new F(function(){return _Od/* s6J9 */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Oc/* s6IW */);
      }
    }
  }
},
_Oh/* getRadioValue2 */ = "(function (elId) { return $(elId); })",
_Oi/* getRadioValue3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\']:checked"));
}),
_Oj/* getRadioValue4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("[name=\'"));
}),
_Ok/* getRadioValue1 */ = function(_Ol/* snXa */, _/* EXTERNAL */){
  var _Om/* snXl */ = eval/* EXTERNAL */(E(_Oh/* FormEngine.JQuery.getRadioValue2 */)),
  _On/* snXt */ = E(_Om/* snXl */)(toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Oj/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_Ol/* snXa */, _Oi/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _Oo/* snXz */ = E(_3S/* FormEngine.JQuery.getRadioValue_f1 */)(_On/* snXt */);
  return new T(function(){
    var _Op/* snXD */ = String/* EXTERNAL */(_Oo/* snXz */);
    return fromJSStr/* EXTERNAL */(_Op/* snXD */);
  });
},
_Oq/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("undefined"));
}),
_Or/* nfiUnitId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_unit"));
}),
_Os/* readEither6 */ = function(_Ot/*  s2Rf3 */){
  while(1){
    var _Ou/*  readEither6 */ = B((function(_Ov/* s2Rf3 */){
      var _Ow/* s2Rf4 */ = E(_Ov/* s2Rf3 */);
      if(!_Ow/* s2Rf4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _Ox/* s2Rf6 */ = _Ow/* s2Rf4 */.b,
        _Oy/* s2Rf7 */ = E(_Ow/* s2Rf4 */.a);
        if(!E(_Oy/* s2Rf7 */.b)._){
          return new T2(1,_Oy/* s2Rf7 */.a,new T(function(){
            return B(_Os/* Text.Read.readEither6 */(_Ox/* s2Rf6 */));
          }));
        }else{
          _Ot/*  s2Rf3 */ = _Ox/* s2Rf6 */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_Ot/*  s2Rf3 */));
    if(_Ou/*  readEither6 */!=__continue/* EXTERNAL */){
      return _Ou/*  readEither6 */;
    }
  }
},
_Oz/* run */ = function(_OA/*  s1iAI */, _OB/*  s1iAJ */){
  while(1){
    var _OC/*  run */ = B((function(_OD/* s1iAI */, _OE/* s1iAJ */){
      var _OF/* s1iAK */ = E(_OD/* s1iAI */);
      switch(_OF/* s1iAK */._){
        case 0:
          var _OG/* s1iAM */ = E(_OE/* s1iAJ */);
          if(!_OG/* s1iAM */._){
            return __Z/* EXTERNAL */;
          }else{
            _OA/*  s1iAI */ = B(A1(_OF/* s1iAK */.a,_OG/* s1iAM */.a));
            _OB/*  s1iAJ */ = _OG/* s1iAM */.b;
            return __continue/* EXTERNAL */;
          }
          break;
        case 1:
          var _OH/*   s1iAI */ = B(A1(_OF/* s1iAK */.a,_OE/* s1iAJ */)),
          _OI/*   s1iAJ */ = _OE/* s1iAJ */;
          _OA/*  s1iAI */ = _OH/*   s1iAI */;
          _OB/*  s1iAJ */ = _OI/*   s1iAJ */;
          return __continue/* EXTERNAL */;
        case 2:
          return __Z/* EXTERNAL */;
        case 3:
          return new T2(1,new T2(0,_OF/* s1iAK */.a,_OE/* s1iAJ */),new T(function(){
            return B(_Oz/* Text.ParserCombinators.ReadP.run */(_OF/* s1iAK */.b, _OE/* s1iAJ */));
          }));
        default:
          return E(_OF/* s1iAK */.a);
      }
    })(_OA/*  s1iAI */, _OB/*  s1iAJ */));
    if(_OC/*  run */!=__continue/* EXTERNAL */){
      return _OC/*  run */;
    }
  }
},
_OJ/* selectByName2 */ = "(function (name) { return $(\'[name=\"\' + name + \'\"]\'); })",
_OK/* selectByName1 */ = function(_OL/* snUw */, _/* EXTERNAL */){
  var _OM/* snUG */ = eval/* EXTERNAL */(E(_OJ/* FormEngine.JQuery.selectByName2 */));
  return new F(function(){return E(_OM/* snUG */)(toJSStr/* EXTERNAL */(E(_OL/* snUw */)));});
},
_ON/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_OO/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_OP/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_OQ/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_ON/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_OO/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_OP/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_OR/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_OQ/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_OS/* $fExceptionPatternMatchFail1 */ = function(_OT/* s4nv1 */){
  return E(_OR/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_OU/* $fExceptionPatternMatchFail_$cfromException */ = function(_OV/* s4nvc */){
  var _OW/* s4nvd */ = E(_OV/* s4nvc */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_OW/* s4nvd */.a)), _OS/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _OW/* s4nvd */.b);});
},
_OX/* $fExceptionPatternMatchFail_$cshow */ = function(_OY/* s4nv4 */){
  return E(E(_OY/* s4nv4 */).a);
},
_OZ/* $fExceptionPatternMatchFail_$ctoException */ = function(_P0/* B1 */){
  return new T2(0,_P1/* Control.Exception.Base.$fExceptionPatternMatchFail */,_P0/* B1 */);
},
_P2/* $fShowPatternMatchFail1 */ = function(_P3/* s4nqK */, _P4/* s4nqL */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_P3/* s4nqK */).a, _P4/* s4nqL */);});
},
_P5/* $fShowPatternMatchFail_$cshowList */ = function(_P6/* s4nv2 */, _P7/* s4nv3 */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_P2/* Control.Exception.Base.$fShowPatternMatchFail1 */, _P6/* s4nv2 */, _P7/* s4nv3 */);});
},
_P8/* $fShowPatternMatchFail_$cshowsPrec */ = function(_P9/* s4nv7 */, _Pa/* s4nv8 */, _Pb/* s4nv9 */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_Pa/* s4nv8 */).a, _Pb/* s4nv9 */);});
},
_Pc/* $fShowPatternMatchFail */ = new T3(0,_P8/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_OX/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_P5/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_P1/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_OS/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_Pc/* Control.Exception.Base.$fShowPatternMatchFail */,_OZ/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_OU/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_OX/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_Pd/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_Pe/* lvl */ = function(_Pf/* s2SzX */, _Pg/* s2SzY */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_Pg/* s2SzY */, _Pf/* s2SzX */));
  }));});
},
_Ph/* throw1 */ = function(_Pi/* B2 */, _Pj/* B1 */){
  return new F(function(){return _Pe/* GHC.Exception.lvl */(_Pi/* B2 */, _Pj/* B1 */);});
},
_Pk/* $wspan */ = function(_Pl/* s9vU */, _Pm/* s9vV */){
  var _Pn/* s9vW */ = E(_Pm/* s9vV */);
  if(!_Pn/* s9vW */._){
    return new T2(0,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */);
  }else{
    var _Po/* s9vX */ = _Pn/* s9vW */.a;
    if(!B(A1(_Pl/* s9vU */,_Po/* s9vX */))){
      return new T2(0,_I/* GHC.Types.[] */,_Pn/* s9vW */);
    }else{
      var _Pp/* s9w0 */ = new T(function(){
        var _Pq/* s9w1 */ = B(_Pk/* GHC.List.$wspan */(_Pl/* s9vU */, _Pn/* s9vW */.b));
        return new T2(0,_Pq/* s9w1 */.a,_Pq/* s9w1 */.b);
      });
      return new T2(0,new T2(1,_Po/* s9vX */,new T(function(){
        return E(E(_Pp/* s9w0 */).a);
      })),new T(function(){
        return E(E(_Pp/* s9w0 */).b);
      }));
    }
  }
},
_Pr/* untangle1 */ = 32,
_Ps/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_Pt/* untangle3 */ = function(_Pu/* s3K4R */){
  return (E(_Pu/* s3K4R */)==124) ? false : true;
},
_Pv/* untangle */ = function(_Pw/* s3K5K */, _Px/* s3K5L */){
  var _Py/* s3K5N */ = B(_Pk/* GHC.List.$wspan */(_Pt/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_Pw/* s3K5K */)))),
  _Pz/* s3K5O */ = _Py/* s3K5N */.a,
  _PA/* s3K5Q */ = function(_PB/* s3K5R */, _PC/* s3K5S */){
    var _PD/* s3K5V */ = new T(function(){
      var _PE/* s3K5U */ = new T(function(){
        return B(_12/* GHC.Base.++ */(_Px/* s3K5L */, new T(function(){
          return B(_12/* GHC.Base.++ */(_PC/* s3K5S */, _Ps/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _PE/* s3K5U */));
    },1);
    return new F(function(){return _12/* GHC.Base.++ */(_PB/* s3K5R */, _PD/* s3K5V */);});
  },
  _PF/* s3K5W */ = E(_Py/* s3K5N */.b);
  if(!_PF/* s3K5W */._){
    return new F(function(){return _PA/* s3K5Q */(_Pz/* s3K5O */, _I/* GHC.Types.[] */);});
  }else{
    if(E(_PF/* s3K5W */.a)==124){
      return new F(function(){return _PA/* s3K5Q */(_Pz/* s3K5O */, new T2(1,_Pr/* GHC.IO.Exception.untangle1 */,_PF/* s3K5W */.b));});
    }else{
      return new F(function(){return _PA/* s3K5Q */(_Pz/* s3K5O */, _I/* GHC.Types.[] */);});
    }
  }
},
_PG/* patError */ = function(_PH/* s4nwI */){
  return new F(function(){return _Ph/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_Pv/* GHC.IO.Exception.untangle */(_PH/* s4nwI */, _Pd/* Control.Exception.Base.lvl3 */));
  })), _P1/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_PI/* lvl2 */ = new T(function(){
  return B(_PG/* Control.Exception.Base.patError */("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));
}),
_PJ/* $fAlternativeP_$c<|> */ = function(_PK/* s1iBo */, _PL/* s1iBp */){
  var _PM/* s1iBq */ = function(_PN/* s1iBr */){
    var _PO/* s1iBs */ = E(_PL/* s1iBp */);
    if(_PO/* s1iBs */._==3){
      return new T2(3,_PO/* s1iBs */.a,new T(function(){
        return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_PK/* s1iBo */, _PO/* s1iBs */.b));
      }));
    }else{
      var _PP/* s1iBt */ = E(_PK/* s1iBo */);
      if(_PP/* s1iBt */._==2){
        return E(_PO/* s1iBs */);
      }else{
        var _PQ/* s1iBu */ = E(_PO/* s1iBs */);
        if(_PQ/* s1iBu */._==2){
          return E(_PP/* s1iBt */);
        }else{
          var _PR/* s1iBv */ = function(_PS/* s1iBw */){
            var _PT/* s1iBx */ = E(_PQ/* s1iBu */);
            if(_PT/* s1iBx */._==4){
              var _PU/* s1iBU */ = function(_PV/* s1iBR */){
                return new T1(4,new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_Oz/* Text.ParserCombinators.ReadP.run */(_PP/* s1iBt */, _PV/* s1iBR */)), _PT/* s1iBx */.a));
                }));
              };
              return new T1(1,_PU/* s1iBU */);
            }else{
              var _PW/* s1iBy */ = E(_PP/* s1iBt */);
              if(_PW/* s1iBy */._==1){
                var _PX/* s1iBF */ = _PW/* s1iBy */.a,
                _PY/* s1iBG */ = E(_PT/* s1iBx */);
                if(!_PY/* s1iBG */._){
                  return new T1(1,function(_PZ/* s1iBI */){
                    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_PX/* s1iBF */,_PZ/* s1iBI */)), _PY/* s1iBG */);});
                  });
                }else{
                  var _Q0/* s1iBP */ = function(_Q1/* s1iBM */){
                    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_PX/* s1iBF */,_Q1/* s1iBM */)), new T(function(){
                      return B(A1(_PY/* s1iBG */.a,_Q1/* s1iBM */));
                    }));});
                  };
                  return new T1(1,_Q0/* s1iBP */);
                }
              }else{
                var _Q2/* s1iBz */ = E(_PT/* s1iBx */);
                if(!_Q2/* s1iBz */._){
                  return E(_PI/* Text.ParserCombinators.ReadP.lvl2 */);
                }else{
                  var _Q3/* s1iBE */ = function(_Q4/* s1iBC */){
                    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_PW/* s1iBy */, new T(function(){
                      return B(A1(_Q2/* s1iBz */.a,_Q4/* s1iBC */));
                    }));});
                  };
                  return new T1(1,_Q3/* s1iBE */);
                }
              }
            }
          },
          _Q5/* s1iBV */ = E(_PP/* s1iBt */);
          switch(_Q5/* s1iBV */._){
            case 1:
              var _Q6/* s1iBX */ = E(_PQ/* s1iBu */);
              if(_Q6/* s1iBX */._==4){
                var _Q7/* s1iC3 */ = function(_Q8/* s1iBZ */){
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_Oz/* Text.ParserCombinators.ReadP.run */(B(A1(_Q5/* s1iBV */.a,_Q8/* s1iBZ */)), _Q8/* s1iBZ */)), _Q6/* s1iBX */.a));
                  }));
                };
                return new T1(1,_Q7/* s1iC3 */);
              }else{
                return new F(function(){return _PR/* s1iBv */(_/* EXTERNAL */);});
              }
              break;
            case 4:
              var _Q9/* s1iC4 */ = _Q5/* s1iBV */.a,
              _Qa/* s1iC5 */ = E(_PQ/* s1iBu */);
              switch(_Qa/* s1iC5 */._){
                case 0:
                  var _Qb/* s1iCa */ = function(_Qc/* s1iC7 */){
                    var _Qd/* s1iC9 */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_Q9/* s1iC4 */, new T(function(){
                        return B(_Oz/* Text.ParserCombinators.ReadP.run */(_Qa/* s1iC5 */, _Qc/* s1iC7 */));
                      },1)));
                    });
                    return new T1(4,_Qd/* s1iC9 */);
                  };
                  return new T1(1,_Qb/* s1iCa */);
                case 1:
                  var _Qe/* s1iCg */ = function(_Qf/* s1iCc */){
                    var _Qg/* s1iCf */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_Q9/* s1iC4 */, new T(function(){
                        return B(_Oz/* Text.ParserCombinators.ReadP.run */(B(A1(_Qa/* s1iC5 */.a,_Qf/* s1iCc */)), _Qf/* s1iCc */));
                      },1)));
                    });
                    return new T1(4,_Qg/* s1iCf */);
                  };
                  return new T1(1,_Qe/* s1iCg */);
                default:
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(_Q9/* s1iC4 */, _Qa/* s1iC5 */.a));
                  }));
              }
              break;
            default:
              return new F(function(){return _PR/* s1iBv */(_/* EXTERNAL */);});
          }
        }
      }
    }
  },
  _Qh/* s1iCm */ = E(_PK/* s1iBo */);
  switch(_Qh/* s1iCm */._){
    case 0:
      var _Qi/* s1iCo */ = E(_PL/* s1iBp */);
      if(!_Qi/* s1iCo */._){
        var _Qj/* s1iCt */ = function(_Qk/* s1iCq */){
          return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_Qh/* s1iCm */.a,_Qk/* s1iCq */)), new T(function(){
            return B(A1(_Qi/* s1iCo */.a,_Qk/* s1iCq */));
          }));});
        };
        return new T1(0,_Qj/* s1iCt */);
      }else{
        return new F(function(){return _PM/* s1iBq */(_/* EXTERNAL */);});
      }
      break;
    case 3:
      return new T2(3,_Qh/* s1iCm */.a,new T(function(){
        return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_Qh/* s1iCm */.b, _PL/* s1iBp */));
      }));
    default:
      return new F(function(){return _PM/* s1iBq */(_/* EXTERNAL */);});
  }
},
_Ql/* $fRead(,)3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_Qm/* $fRead(,)4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_Qn/* $fEqChar_$c/= */ = function(_Qo/* scFn */, _Qp/* scFo */){
  return E(_Qo/* scFn */)!=E(_Qp/* scFo */);
},
_Qq/* $fEqChar_$c== */ = function(_Qr/* scFu */, _Qs/* scFv */){
  return E(_Qr/* scFu */)==E(_Qs/* scFv */);
},
_Qt/* $fEqChar */ = new T2(0,_Qq/* GHC.Classes.$fEqChar_$c== */,_Qn/* GHC.Classes.$fEqChar_$c/= */),
_Qu/* $fEq[]_$s$c==1 */ = function(_Qv/* scIY */, _Qw/* scIZ */){
  while(1){
    var _Qx/* scJ0 */ = E(_Qv/* scIY */);
    if(!_Qx/* scJ0 */._){
      return (E(_Qw/* scIZ */)._==0) ? true : false;
    }else{
      var _Qy/* scJ6 */ = E(_Qw/* scIZ */);
      if(!_Qy/* scJ6 */._){
        return false;
      }else{
        if(E(_Qx/* scJ0 */.a)!=E(_Qy/* scJ6 */.a)){
          return false;
        }else{
          _Qv/* scIY */ = _Qx/* scJ0 */.b;
          _Qw/* scIZ */ = _Qy/* scJ6 */.b;
          continue;
        }
      }
    }
  }
},
_Qz/* $fEq[]_$s$c/=1 */ = function(_QA/* scJE */, _QB/* scJF */){
  return (!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_QA/* scJE */, _QB/* scJF */))) ? true : false;
},
_QC/* $fEq[]_$s$fEq[]1 */ = new T2(0,_Qu/* GHC.Classes.$fEq[]_$s$c==1 */,_Qz/* GHC.Classes.$fEq[]_$s$c/=1 */),
_QD/* $fAlternativeP_$c>>= */ = function(_QE/* s1iCx */, _QF/* s1iCy */){
  var _QG/* s1iCz */ = E(_QE/* s1iCx */);
  switch(_QG/* s1iCz */._){
    case 0:
      return new T1(0,function(_QH/* s1iCB */){
        return new F(function(){return _QD/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_QG/* s1iCz */.a,_QH/* s1iCB */)), _QF/* s1iCy */);});
      });
    case 1:
      return new T1(1,function(_QI/* s1iCF */){
        return new F(function(){return _QD/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_QG/* s1iCz */.a,_QI/* s1iCF */)), _QF/* s1iCy */);});
      });
    case 2:
      return new T0(2);
    case 3:
      return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_QF/* s1iCy */,_QG/* s1iCz */.a)), new T(function(){
        return B(_QD/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_QG/* s1iCz */.b, _QF/* s1iCy */));
      }));});
      break;
    default:
      var _QJ/* s1iCN */ = function(_QK/* s1iCO */){
        var _QL/* s1iCP */ = E(_QK/* s1iCO */);
        if(!_QL/* s1iCP */._){
          return __Z/* EXTERNAL */;
        }else{
          var _QM/* s1iCS */ = E(_QL/* s1iCP */.a);
          return new F(function(){return _12/* GHC.Base.++ */(B(_Oz/* Text.ParserCombinators.ReadP.run */(B(A1(_QF/* s1iCy */,_QM/* s1iCS */.a)), _QM/* s1iCS */.b)), new T(function(){
            return B(_QJ/* s1iCN */(_QL/* s1iCP */.b));
          },1));});
        }
      },
      _QN/* s1iCY */ = B(_QJ/* s1iCN */(_QG/* s1iCz */.a));
      return (_QN/* s1iCY */._==0) ? new T0(2) : new T1(4,_QN/* s1iCY */);
  }
},
_QO/* Fail */ = new T0(2),
_QP/* $fApplicativeP_$creturn */ = function(_QQ/* s1iBl */){
  return new T2(3,_QQ/* s1iBl */,_QO/* Text.ParserCombinators.ReadP.Fail */);
},
_QR/* <++2 */ = function(_QS/* s1iyp */, _QT/* s1iyq */){
  var _QU/* s1iyr */ = E(_QS/* s1iyp */);
  if(!_QU/* s1iyr */){
    return new F(function(){return A1(_QT/* s1iyq */,_0/* GHC.Tuple.() */);});
  }else{
    var _QV/* s1iys */ = new T(function(){
      return B(_QR/* Text.ParserCombinators.ReadP.<++2 */(_QU/* s1iyr */-1|0, _QT/* s1iyq */));
    });
    return new T1(0,function(_QW/* s1iyu */){
      return E(_QV/* s1iys */);
    });
  }
},
_QX/* $wa */ = function(_QY/* s1iD8 */, _QZ/* s1iD9 */, _R0/* s1iDa */){
  var _R1/* s1iDb */ = new T(function(){
    return B(A1(_QY/* s1iD8 */,_QP/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
  }),
  _R2/* s1iDc */ = function(_R3/*  s1iDd */, _R4/*  s1iDe */, _R5/*  s1iDf */, _R6/*  s1iDg */){
    while(1){
      var _R7/*  s1iDc */ = B((function(_R8/* s1iDd */, _R9/* s1iDe */, _Ra/* s1iDf */, _Rb/* s1iDg */){
        var _Rc/* s1iDh */ = E(_R8/* s1iDd */);
        switch(_Rc/* s1iDh */._){
          case 0:
            var _Rd/* s1iDj */ = E(_R9/* s1iDe */);
            if(!_Rd/* s1iDj */._){
              return new F(function(){return A1(_QZ/* s1iD9 */,_Rb/* s1iDg */);});
            }else{
              var _Re/*   s1iDf */ = _Ra/* s1iDf */+1|0,
              _Rf/*   s1iDg */ = _Rb/* s1iDg */;
              _R3/*  s1iDd */ = B(A1(_Rc/* s1iDh */.a,_Rd/* s1iDj */.a));
              _R4/*  s1iDe */ = _Rd/* s1iDj */.b;
              _R5/*  s1iDf */ = _Re/*   s1iDf */;
              _R6/*  s1iDg */ = _Rf/*   s1iDg */;
              return __continue/* EXTERNAL */;
            }
            break;
          case 1:
            var _Rg/*   s1iDd */ = B(A1(_Rc/* s1iDh */.a,_R9/* s1iDe */)),
            _Rh/*   s1iDe */ = _R9/* s1iDe */,
            _Re/*   s1iDf */ = _Ra/* s1iDf */,
            _Rf/*   s1iDg */ = _Rb/* s1iDg */;
            _R3/*  s1iDd */ = _Rg/*   s1iDd */;
            _R4/*  s1iDe */ = _Rh/*   s1iDe */;
            _R5/*  s1iDf */ = _Re/*   s1iDf */;
            _R6/*  s1iDg */ = _Rf/*   s1iDg */;
            return __continue/* EXTERNAL */;
          case 2:
            return new F(function(){return A1(_QZ/* s1iD9 */,_Rb/* s1iDg */);});
            break;
          case 3:
            var _Ri/* s1iDs */ = new T(function(){
              return B(_QD/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Rc/* s1iDh */, _Rb/* s1iDg */));
            });
            return new F(function(){return _QR/* Text.ParserCombinators.ReadP.<++2 */(_Ra/* s1iDf */, function(_Rj/* s1iDt */){
              return E(_Ri/* s1iDs */);
            });});
            break;
          default:
            return new F(function(){return _QD/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Rc/* s1iDh */, _Rb/* s1iDg */);});
        }
      })(_R3/*  s1iDd */, _R4/*  s1iDe */, _R5/*  s1iDf */, _R6/*  s1iDg */));
      if(_R7/*  s1iDc */!=__continue/* EXTERNAL */){
        return _R7/*  s1iDc */;
      }
    }
  };
  return function(_Rk/* s1iDw */){
    return new F(function(){return _R2/* s1iDc */(_R1/* s1iDb */, _Rk/* s1iDw */, 0, _R0/* s1iDa */);});
  };
},
_Rl/* munch3 */ = function(_Rm/* s1iyo */){
  return new F(function(){return A1(_Rm/* s1iyo */,_I/* GHC.Types.[] */);});
},
_Rn/* $wa3 */ = function(_Ro/* s1iyQ */, _Rp/* s1iyR */){
  var _Rq/* s1iyS */ = function(_Rr/* s1iyT */){
    var _Rs/* s1iyU */ = E(_Rr/* s1iyT */);
    if(!_Rs/* s1iyU */._){
      return E(_Rl/* Text.ParserCombinators.ReadP.munch3 */);
    }else{
      var _Rt/* s1iyV */ = _Rs/* s1iyU */.a;
      if(!B(A1(_Ro/* s1iyQ */,_Rt/* s1iyV */))){
        return E(_Rl/* Text.ParserCombinators.ReadP.munch3 */);
      }else{
        var _Ru/* s1iyY */ = new T(function(){
          return B(_Rq/* s1iyS */(_Rs/* s1iyU */.b));
        }),
        _Rv/* s1iz6 */ = function(_Rw/* s1iyZ */){
          var _Rx/* s1iz0 */ = new T(function(){
            return B(A1(_Ru/* s1iyY */,function(_Ry/* s1iz1 */){
              return new F(function(){return A1(_Rw/* s1iyZ */,new T2(1,_Rt/* s1iyV */,_Ry/* s1iz1 */));});
            }));
          });
          return new T1(0,function(_Rz/* s1iz4 */){
            return E(_Rx/* s1iz0 */);
          });
        };
        return E(_Rv/* s1iz6 */);
      }
    }
  };
  return function(_RA/* s1iz7 */){
    return new F(function(){return A2(_Rq/* s1iyS */,_RA/* s1iz7 */, _Rp/* s1iyR */);});
  };
},
_RB/* EOF */ = new T0(6),
_RC/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("valDig: Bad base"));
}),
_RD/* readDecP2 */ = new T(function(){
  return B(err/* EXTERNAL */(_RC/* Text.Read.Lex.lvl37 */));
}),
_RE/* $wa6 */ = function(_RF/* s1oaO */, _RG/* s1oaP */){
  var _RH/* s1oaQ */ = function(_RI/* s1oaR */, _RJ/* s1oaS */){
    var _RK/* s1oaT */ = E(_RI/* s1oaR */);
    if(!_RK/* s1oaT */._){
      var _RL/* s1oaU */ = new T(function(){
        return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
      });
      return function(_RM/* s1oaV */){
        return new F(function(){return A1(_RM/* s1oaV */,_RL/* s1oaU */);});
      };
    }else{
      var _RN/* s1ob1 */ = E(_RK/* s1oaT */.a),
      _RO/* s1ob3 */ = function(_RP/* s1ob4 */){
        var _RQ/* s1ob5 */ = new T(function(){
          return B(_RH/* s1oaQ */(_RK/* s1oaT */.b, function(_RR/* s1ob6 */){
            return new F(function(){return A1(_RJ/* s1oaS */,new T2(1,_RP/* s1ob4 */,_RR/* s1ob6 */));});
          }));
        }),
        _RS/* s1obd */ = function(_RT/* s1ob9 */){
          var _RU/* s1oba */ = new T(function(){
            return B(A1(_RQ/* s1ob5 */,_RT/* s1ob9 */));
          });
          return new T1(0,function(_RV/* s1obb */){
            return E(_RU/* s1oba */);
          });
        };
        return E(_RS/* s1obd */);
      };
      switch(E(_RF/* s1oaO */)){
        case 8:
          if(48>_RN/* s1ob1 */){
            var _RW/* s1obi */ = new T(function(){
              return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_RX/* s1obj */){
              return new F(function(){return A1(_RX/* s1obj */,_RW/* s1obi */);});
            };
          }else{
            if(_RN/* s1ob1 */>55){
              var _RY/* s1obn */ = new T(function(){
                return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_RZ/* s1obo */){
                return new F(function(){return A1(_RZ/* s1obo */,_RY/* s1obn */);});
              };
            }else{
              return new F(function(){return _RO/* s1ob3 */(_RN/* s1ob1 */-48|0);});
            }
          }
          break;
        case 10:
          if(48>_RN/* s1ob1 */){
            var _S0/* s1obv */ = new T(function(){
              return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_S1/* s1obw */){
              return new F(function(){return A1(_S1/* s1obw */,_S0/* s1obv */);});
            };
          }else{
            if(_RN/* s1ob1 */>57){
              var _S2/* s1obA */ = new T(function(){
                return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_S3/* s1obB */){
                return new F(function(){return A1(_S3/* s1obB */,_S2/* s1obA */);});
              };
            }else{
              return new F(function(){return _RO/* s1ob3 */(_RN/* s1ob1 */-48|0);});
            }
          }
          break;
        case 16:
          if(48>_RN/* s1ob1 */){
            if(97>_RN/* s1ob1 */){
              if(65>_RN/* s1ob1 */){
                var _S4/* s1obM */ = new T(function(){
                  return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                });
                return function(_S5/* s1obN */){
                  return new F(function(){return A1(_S5/* s1obN */,_S4/* s1obM */);});
                };
              }else{
                if(_RN/* s1ob1 */>70){
                  var _S6/* s1obR */ = new T(function(){
                    return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_S7/* s1obS */){
                    return new F(function(){return A1(_S7/* s1obS */,_S6/* s1obR */);});
                  };
                }else{
                  return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-65|0)+10|0);});
                }
              }
            }else{
              if(_RN/* s1ob1 */>102){
                if(65>_RN/* s1ob1 */){
                  var _S8/* s1oc2 */ = new T(function(){
                    return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_S9/* s1oc3 */){
                    return new F(function(){return A1(_S9/* s1oc3 */,_S8/* s1oc2 */);});
                  };
                }else{
                  if(_RN/* s1ob1 */>70){
                    var _Sa/* s1oc7 */ = new T(function(){
                      return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Sb/* s1oc8 */){
                      return new F(function(){return A1(_Sb/* s1oc8 */,_Sa/* s1oc7 */);});
                    };
                  }else{
                    return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-97|0)+10|0);});
              }
            }
          }else{
            if(_RN/* s1ob1 */>57){
              if(97>_RN/* s1ob1 */){
                if(65>_RN/* s1ob1 */){
                  var _Sc/* s1oco */ = new T(function(){
                    return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_Sd/* s1ocp */){
                    return new F(function(){return A1(_Sd/* s1ocp */,_Sc/* s1oco */);});
                  };
                }else{
                  if(_RN/* s1ob1 */>70){
                    var _Se/* s1oct */ = new T(function(){
                      return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Sf/* s1ocu */){
                      return new F(function(){return A1(_Sf/* s1ocu */,_Se/* s1oct */);});
                    };
                  }else{
                    return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                if(_RN/* s1ob1 */>102){
                  if(65>_RN/* s1ob1 */){
                    var _Sg/* s1ocE */ = new T(function(){
                      return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Sh/* s1ocF */){
                      return new F(function(){return A1(_Sh/* s1ocF */,_Sg/* s1ocE */);});
                    };
                  }else{
                    if(_RN/* s1ob1 */>70){
                      var _Si/* s1ocJ */ = new T(function(){
                        return B(A1(_RJ/* s1oaS */,_I/* GHC.Types.[] */));
                      });
                      return function(_Sj/* s1ocK */){
                        return new F(function(){return A1(_Sj/* s1ocK */,_Si/* s1ocJ */);});
                      };
                    }else{
                      return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-65|0)+10|0);});
                    }
                  }
                }else{
                  return new F(function(){return _RO/* s1ob3 */((_RN/* s1ob1 */-97|0)+10|0);});
                }
              }
            }else{
              return new F(function(){return _RO/* s1ob3 */(_RN/* s1ob1 */-48|0);});
            }
          }
          break;
        default:
          return E(_RD/* Text.Read.Lex.readDecP2 */);
      }
    }
  },
  _Sk/* s1ocX */ = function(_Sl/* s1ocY */){
    var _Sm/* s1ocZ */ = E(_Sl/* s1ocY */);
    if(!_Sm/* s1ocZ */._){
      return new T0(2);
    }else{
      return new F(function(){return A1(_RG/* s1oaP */,_Sm/* s1ocZ */);});
    }
  };
  return function(_Sn/* s1od2 */){
    return new F(function(){return A3(_RH/* s1oaQ */,_Sn/* s1od2 */, _4/* GHC.Base.id */, _Sk/* s1ocX */);});
  };
},
_So/* lvl41 */ = 16,
_Sp/* lvl42 */ = 8,
_Sq/* $wa7 */ = function(_Sr/* s1od4 */){
  var _Ss/* s1od5 */ = function(_St/* s1od6 */){
    return new F(function(){return A1(_Sr/* s1od4 */,new T1(5,new T2(0,_Sp/* Text.Read.Lex.lvl42 */,_St/* s1od6 */)));});
  },
  _Su/* s1od9 */ = function(_Sv/* s1oda */){
    return new F(function(){return A1(_Sr/* s1od4 */,new T1(5,new T2(0,_So/* Text.Read.Lex.lvl41 */,_Sv/* s1oda */)));});
  },
  _Sw/* s1odd */ = function(_Sx/* s1ode */){
    switch(E(_Sx/* s1ode */)){
      case 79:
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_Sp/* Text.Read.Lex.lvl42 */, _Ss/* s1od5 */)));
      case 88:
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_So/* Text.Read.Lex.lvl41 */, _Su/* s1od9 */)));
      case 111:
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_Sp/* Text.Read.Lex.lvl42 */, _Ss/* s1od5 */)));
      case 120:
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_So/* Text.Read.Lex.lvl41 */, _Su/* s1od9 */)));
      default:
        return new T0(2);
    }
  };
  return function(_Sy/* s1odr */){
    return (E(_Sy/* s1odr */)==48) ? E(new T1(0,_Sw/* s1odd */)) : new T0(2);
  };
},
_Sz/* a2 */ = function(_SA/* s1odw */){
  return new T1(0,B(_Sq/* Text.Read.Lex.$wa7 */(_SA/* s1odw */)));
},
_SB/* a */ = function(_SC/* s1o94 */){
  return new F(function(){return A1(_SC/* s1o94 */,_2o/* GHC.Base.Nothing */);});
},
_SD/* a1 */ = function(_SE/* s1o95 */){
  return new F(function(){return A1(_SE/* s1o95 */,_2o/* GHC.Base.Nothing */);});
},
_SF/* lvl */ = 10,
_SG/* log2I1 */ = new T1(0,1),
_SH/* lvl2 */ = new T1(0,2147483647),
_SI/* plusInteger */ = function(_SJ/* s1Qe */, _SK/* s1Qf */){
  while(1){
    var _SL/* s1Qg */ = E(_SJ/* s1Qe */);
    if(!_SL/* s1Qg */._){
      var _SM/* s1Qh */ = _SL/* s1Qg */.a,
      _SN/* s1Qi */ = E(_SK/* s1Qf */);
      if(!_SN/* s1Qi */._){
        var _SO/* s1Qj */ = _SN/* s1Qi */.a,
        _SP/* s1Qk */ = addC/* EXTERNAL */(_SM/* s1Qh */, _SO/* s1Qj */);
        if(!E(_SP/* s1Qk */.b)){
          return new T1(0,_SP/* s1Qk */.a);
        }else{
          _SJ/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_SM/* s1Qh */));
          _SK/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_SO/* s1Qj */));
          continue;
        }
      }else{
        _SJ/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_SM/* s1Qh */));
        _SK/* s1Qf */ = _SN/* s1Qi */;
        continue;
      }
    }else{
      var _SQ/* s1Qz */ = E(_SK/* s1Qf */);
      if(!_SQ/* s1Qz */._){
        _SJ/* s1Qe */ = _SL/* s1Qg */;
        _SK/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_SQ/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_SL/* s1Qg */.a, _SQ/* s1Qz */.a));
      }
    }
  }
},
_SR/* lvl3 */ = new T(function(){
  return B(_SI/* GHC.Integer.Type.plusInteger */(_SH/* GHC.Integer.Type.lvl2 */, _SG/* GHC.Integer.Type.log2I1 */));
}),
_SS/* negateInteger */ = function(_ST/* s1QH */){
  var _SU/* s1QI */ = E(_ST/* s1QH */);
  if(!_SU/* s1QI */._){
    var _SV/* s1QK */ = E(_SU/* s1QI */.a);
    return (_SV/* s1QK */==(-2147483648)) ? E(_SR/* GHC.Integer.Type.lvl3 */) : new T1(0, -_SV/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_SU/* s1QI */.a));
  }
},
_SW/* numberToFixed1 */ = new T1(0,10),
_SX/* $wlenAcc */ = function(_SY/* s9Bd */, _SZ/* s9Be */){
  while(1){
    var _T0/* s9Bf */ = E(_SY/* s9Bd */);
    if(!_T0/* s9Bf */._){
      return E(_SZ/* s9Be */);
    }else{
      var _T1/*  s9Be */ = _SZ/* s9Be */+1|0;
      _SY/* s9Bd */ = _T0/* s9Bf */.b;
      _SZ/* s9Be */ = _T1/*  s9Be */;
      continue;
    }
  }
},
_T2/* smallInteger */ = function(_T3/* B1 */){
  return new T1(0,_T3/* B1 */);
},
_T4/* numberToFixed2 */ = function(_T5/* s1o9e */){
  return new F(function(){return _T2/* GHC.Integer.Type.smallInteger */(E(_T5/* s1o9e */));});
},
_T6/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("this should not happen"));
}),
_T7/* lvl40 */ = new T(function(){
  return B(err/* EXTERNAL */(_T6/* Text.Read.Lex.lvl39 */));
}),
_T8/* timesInteger */ = function(_T9/* s1PN */, _Ta/* s1PO */){
  while(1){
    var _Tb/* s1PP */ = E(_T9/* s1PN */);
    if(!_Tb/* s1PP */._){
      var _Tc/* s1PQ */ = _Tb/* s1PP */.a,
      _Td/* s1PR */ = E(_Ta/* s1PO */);
      if(!_Td/* s1PR */._){
        var _Te/* s1PS */ = _Td/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_Tc/* s1PQ */, _Te/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_Tc/* s1PQ */, _Te/* s1PS */)|0);
        }else{
          _T9/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Tc/* s1PQ */));
          _Ta/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Te/* s1PS */));
          continue;
        }
      }else{
        _T9/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Tc/* s1PQ */));
        _Ta/* s1PO */ = _Td/* s1PR */;
        continue;
      }
    }else{
      var _Tf/* s1Q6 */ = E(_Ta/* s1PO */);
      if(!_Tf/* s1Q6 */._){
        _T9/* s1PN */ = _Tb/* s1PP */;
        _Ta/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Tf/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_Tb/* s1PP */.a, _Tf/* s1Q6 */.a));
      }
    }
  }
},
_Tg/* combine */ = function(_Th/* s1o9h */, _Ti/* s1o9i */){
  var _Tj/* s1o9j */ = E(_Ti/* s1o9i */);
  if(!_Tj/* s1o9j */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Tk/* s1o9m */ = E(_Tj/* s1o9j */.b);
    return (_Tk/* s1o9m */._==0) ? E(_T7/* Text.Read.Lex.lvl40 */) : new T2(1,B(_SI/* GHC.Integer.Type.plusInteger */(B(_T8/* GHC.Integer.Type.timesInteger */(_Tj/* s1o9j */.a, _Th/* s1o9h */)), _Tk/* s1o9m */.a)),new T(function(){
      return B(_Tg/* Text.Read.Lex.combine */(_Th/* s1o9h */, _Tk/* s1o9m */.b));
    }));
  }
},
_Tl/* numberToFixed3 */ = new T1(0,0),
_Tm/* numberToFixed_go */ = function(_Tn/*  s1o9s */, _To/*  s1o9t */, _Tp/*  s1o9u */){
  while(1){
    var _Tq/*  numberToFixed_go */ = B((function(_Tr/* s1o9s */, _Ts/* s1o9t */, _Tt/* s1o9u */){
      var _Tu/* s1o9v */ = E(_Tt/* s1o9u */);
      if(!_Tu/* s1o9v */._){
        return E(_Tl/* Text.Read.Lex.numberToFixed3 */);
      }else{
        if(!E(_Tu/* s1o9v */.b)._){
          return E(_Tu/* s1o9v */.a);
        }else{
          var _Tv/* s1o9B */ = E(_Ts/* s1o9t */);
          if(_Tv/* s1o9B */<=40){
            var _Tw/* s1o9F */ = function(_Tx/* s1o9G */, _Ty/* s1o9H */){
              while(1){
                var _Tz/* s1o9I */ = E(_Ty/* s1o9H */);
                if(!_Tz/* s1o9I */._){
                  return E(_Tx/* s1o9G */);
                }else{
                  var _TA/*  s1o9G */ = B(_SI/* GHC.Integer.Type.plusInteger */(B(_T8/* GHC.Integer.Type.timesInteger */(_Tx/* s1o9G */, _Tr/* s1o9s */)), _Tz/* s1o9I */.a));
                  _Tx/* s1o9G */ = _TA/*  s1o9G */;
                  _Ty/* s1o9H */ = _Tz/* s1o9I */.b;
                  continue;
                }
              }
            };
            return new F(function(){return _Tw/* s1o9F */(_Tl/* Text.Read.Lex.numberToFixed3 */, _Tu/* s1o9v */);});
          }else{
            var _TB/* s1o9N */ = B(_T8/* GHC.Integer.Type.timesInteger */(_Tr/* s1o9s */, _Tr/* s1o9s */));
            if(!(_Tv/* s1o9B */%2)){
              var _TC/*   s1o9u */ = B(_Tg/* Text.Read.Lex.combine */(_Tr/* s1o9s */, _Tu/* s1o9v */));
              _Tn/*  s1o9s */ = _TB/* s1o9N */;
              _To/*  s1o9t */ = quot/* EXTERNAL */(_Tv/* s1o9B */+1|0, 2);
              _Tp/*  s1o9u */ = _TC/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }else{
              var _TC/*   s1o9u */ = B(_Tg/* Text.Read.Lex.combine */(_Tr/* s1o9s */, new T2(1,_Tl/* Text.Read.Lex.numberToFixed3 */,_Tu/* s1o9v */)));
              _Tn/*  s1o9s */ = _TB/* s1o9N */;
              _To/*  s1o9t */ = quot/* EXTERNAL */(_Tv/* s1o9B */+1|0, 2);
              _Tp/*  s1o9u */ = _TC/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }
          }
        }
      }
    })(_Tn/*  s1o9s */, _To/*  s1o9t */, _Tp/*  s1o9u */));
    if(_Tq/*  numberToFixed_go */!=__continue/* EXTERNAL */){
      return _Tq/*  numberToFixed_go */;
    }
  }
},
_TD/* valInteger */ = function(_TE/* s1off */, _TF/* s1ofg */){
  return new F(function(){return _Tm/* Text.Read.Lex.numberToFixed_go */(_TE/* s1off */, new T(function(){
    return B(_SX/* GHC.List.$wlenAcc */(_TF/* s1ofg */, 0));
  },1), B(_2S/* GHC.Base.map */(_T4/* Text.Read.Lex.numberToFixed2 */, _TF/* s1ofg */)));});
},
_TG/* a26 */ = function(_TH/* s1og4 */){
  var _TI/* s1og5 */ = new T(function(){
    var _TJ/* s1ogC */ = new T(function(){
      var _TK/* s1ogz */ = function(_TL/* s1ogw */){
        return new F(function(){return A1(_TH/* s1og4 */,new T1(1,new T(function(){
          return B(_TD/* Text.Read.Lex.valInteger */(_SW/* Text.Read.Lex.numberToFixed1 */, _TL/* s1ogw */));
        })));});
      };
      return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_SF/* Text.Read.Lex.lvl */, _TK/* s1ogz */)));
    }),
    _TM/* s1ogt */ = function(_TN/* s1ogj */){
      if(E(_TN/* s1ogj */)==43){
        var _TO/* s1ogq */ = function(_TP/* s1ogn */){
          return new F(function(){return A1(_TH/* s1og4 */,new T1(1,new T(function(){
            return B(_TD/* Text.Read.Lex.valInteger */(_SW/* Text.Read.Lex.numberToFixed1 */, _TP/* s1ogn */));
          })));});
        };
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_SF/* Text.Read.Lex.lvl */, _TO/* s1ogq */)));
      }else{
        return new T0(2);
      }
    },
    _TQ/* s1ogh */ = function(_TR/* s1og6 */){
      if(E(_TR/* s1og6 */)==45){
        var _TS/* s1oge */ = function(_TT/* s1oga */){
          return new F(function(){return A1(_TH/* s1og4 */,new T1(1,new T(function(){
            return B(_SS/* GHC.Integer.Type.negateInteger */(B(_TD/* Text.Read.Lex.valInteger */(_SW/* Text.Read.Lex.numberToFixed1 */, _TT/* s1oga */))));
          })));});
        };
        return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_SF/* Text.Read.Lex.lvl */, _TS/* s1oge */)));
      }else{
        return new T0(2);
      }
    };
    return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_TQ/* s1ogh */), new T1(0,_TM/* s1ogt */))), _TJ/* s1ogC */));
  });
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_TU/* s1ogD */){
    return (E(_TU/* s1ogD */)==101) ? E(_TI/* s1og5 */) : new T0(2);
  }), new T1(0,function(_TV/* s1ogJ */){
    return (E(_TV/* s1ogJ */)==69) ? E(_TI/* s1og5 */) : new T0(2);
  }));});
},
_TW/* $wa8 */ = function(_TX/* s1odz */){
  var _TY/* s1odA */ = function(_TZ/* s1odB */){
    return new F(function(){return A1(_TX/* s1odz */,new T1(1,_TZ/* s1odB */));});
  };
  return function(_U0/* s1odD */){
    return (E(_U0/* s1odD */)==46) ? new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_SF/* Text.Read.Lex.lvl */, _TY/* s1odA */))) : new T0(2);
  };
},
_U1/* a3 */ = function(_U2/* s1odK */){
  return new T1(0,B(_TW/* Text.Read.Lex.$wa8 */(_U2/* s1odK */)));
},
_U3/* $wa10 */ = function(_U4/* s1ogP */){
  var _U5/* s1oh1 */ = function(_U6/* s1ogQ */){
    var _U7/* s1ogY */ = function(_U8/* s1ogR */){
      return new T1(1,B(_QX/* Text.ParserCombinators.ReadP.$wa */(_TG/* Text.Read.Lex.a26 */, _SB/* Text.Read.Lex.a */, function(_U9/* s1ogS */){
        return new F(function(){return A1(_U4/* s1ogP */,new T1(5,new T3(1,_U6/* s1ogQ */,_U8/* s1ogR */,_U9/* s1ogS */)));});
      })));
    };
    return new T1(1,B(_QX/* Text.ParserCombinators.ReadP.$wa */(_U1/* Text.Read.Lex.a3 */, _SD/* Text.Read.Lex.a1 */, _U7/* s1ogY */)));
  };
  return new F(function(){return _RE/* Text.Read.Lex.$wa6 */(_SF/* Text.Read.Lex.lvl */, _U5/* s1oh1 */);});
},
_Ua/* a27 */ = function(_Ub/* s1oh2 */){
  return new T1(1,B(_U3/* Text.Read.Lex.$wa10 */(_Ub/* s1oh2 */)));
},
_Uc/* == */ = function(_Ud/* scBJ */){
  return E(E(_Ud/* scBJ */).a);
},
_Ue/* elem */ = function(_Uf/* s9uW */, _Ug/* s9uX */, _Uh/* s9uY */){
  while(1){
    var _Ui/* s9uZ */ = E(_Uh/* s9uY */);
    if(!_Ui/* s9uZ */._){
      return false;
    }else{
      if(!B(A3(_Uc/* GHC.Classes.== */,_Uf/* s9uW */, _Ug/* s9uX */, _Ui/* s9uZ */.a))){
        _Uh/* s9uY */ = _Ui/* s9uZ */.b;
        continue;
      }else{
        return true;
      }
    }
  }
},
_Uj/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!@#$%&*+./<=>?\\^|:-~"));
}),
_Uk/* a6 */ = function(_Ul/* s1odZ */){
  return new F(function(){return _Ue/* GHC.List.elem */(_Qt/* GHC.Classes.$fEqChar */, _Ul/* s1odZ */, _Uj/* Text.Read.Lex.lvl44 */);});
},
_Um/* $wa9 */ = function(_Un/* s1odN */){
  var _Uo/* s1odO */ = new T(function(){
    return B(A1(_Un/* s1odN */,_Sp/* Text.Read.Lex.lvl42 */));
  }),
  _Up/* s1odP */ = new T(function(){
    return B(A1(_Un/* s1odN */,_So/* Text.Read.Lex.lvl41 */));
  });
  return function(_Uq/* s1odQ */){
    switch(E(_Uq/* s1odQ */)){
      case 79:
        return E(_Uo/* s1odO */);
      case 88:
        return E(_Up/* s1odP */);
      case 111:
        return E(_Uo/* s1odO */);
      case 120:
        return E(_Up/* s1odP */);
      default:
        return new T0(2);
    }
  };
},
_Ur/* a4 */ = function(_Us/* s1odV */){
  return new T1(0,B(_Um/* Text.Read.Lex.$wa9 */(_Us/* s1odV */)));
},
_Ut/* a5 */ = function(_Uu/* s1odY */){
  return new F(function(){return A1(_Uu/* s1odY */,_SF/* Text.Read.Lex.lvl */);});
},
_Uv/* chr2 */ = function(_Uw/* sjTv */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Prelude.chr: bad argument: ", new T(function(){
    return B(_4e/* GHC.Show.$wshowSignedInt */(9, _Uw/* sjTv */, _I/* GHC.Types.[] */));
  }))));});
},
_Ux/* integerToInt */ = function(_Uy/* s1Rv */){
  var _Uz/* s1Rw */ = E(_Uy/* s1Rv */);
  if(!_Uz/* s1Rw */._){
    return E(_Uz/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_Uz/* s1Rw */.a);});
  }
},
_UA/* leInteger */ = function(_UB/* s1Gp */, _UC/* s1Gq */){
  var _UD/* s1Gr */ = E(_UB/* s1Gp */);
  if(!_UD/* s1Gr */._){
    var _UE/* s1Gs */ = _UD/* s1Gr */.a,
    _UF/* s1Gt */ = E(_UC/* s1Gq */);
    return (_UF/* s1Gt */._==0) ? _UE/* s1Gs */<=_UF/* s1Gt */.a : I_compareInt/* EXTERNAL */(_UF/* s1Gt */.a, _UE/* s1Gs */)>=0;
  }else{
    var _UG/* s1GA */ = _UD/* s1Gr */.a,
    _UH/* s1GB */ = E(_UC/* s1Gq */);
    return (_UH/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_UG/* s1GA */, _UH/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_UG/* s1GA */, _UH/* s1GB */.a)<=0;
  }
},
_UI/* pfail1 */ = function(_UJ/* s1izT */){
  return new T0(2);
},
_UK/* choice */ = function(_UL/* s1iDZ */){
  var _UM/* s1iE0 */ = E(_UL/* s1iDZ */);
  if(!_UM/* s1iE0 */._){
    return E(_UI/* Text.ParserCombinators.ReadP.pfail1 */);
  }else{
    var _UN/* s1iE1 */ = _UM/* s1iE0 */.a,
    _UO/* s1iE3 */ = E(_UM/* s1iE0 */.b);
    if(!_UO/* s1iE3 */._){
      return E(_UN/* s1iE1 */);
    }else{
      var _UP/* s1iE6 */ = new T(function(){
        return B(_UK/* Text.ParserCombinators.ReadP.choice */(_UO/* s1iE3 */));
      }),
      _UQ/* s1iEa */ = function(_UR/* s1iE7 */){
        return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_UN/* s1iE1 */,_UR/* s1iE7 */)), new T(function(){
          return B(A1(_UP/* s1iE6 */,_UR/* s1iE7 */));
        }));});
      };
      return E(_UQ/* s1iEa */);
    }
  }
},
_US/* $wa6 */ = function(_UT/* s1izU */, _UU/* s1izV */){
  var _UV/* s1izW */ = function(_UW/* s1izX */, _UX/* s1izY */, _UY/* s1izZ */){
    var _UZ/* s1iA0 */ = E(_UW/* s1izX */);
    if(!_UZ/* s1iA0 */._){
      return new F(function(){return A1(_UY/* s1izZ */,_UT/* s1izU */);});
    }else{
      var _V0/* s1iA3 */ = E(_UX/* s1izY */);
      if(!_V0/* s1iA3 */._){
        return new T0(2);
      }else{
        if(E(_UZ/* s1iA0 */.a)!=E(_V0/* s1iA3 */.a)){
          return new T0(2);
        }else{
          var _V1/* s1iAc */ = new T(function(){
            return B(_UV/* s1izW */(_UZ/* s1iA0 */.b, _V0/* s1iA3 */.b, _UY/* s1izZ */));
          });
          return new T1(0,function(_V2/* s1iAd */){
            return E(_V1/* s1iAc */);
          });
        }
      }
    }
  };
  return function(_V3/* s1iAf */){
    return new F(function(){return _UV/* s1izW */(_UT/* s1izU */, _V3/* s1iAf */, _UU/* s1izV */);});
  };
},
_V4/* a28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_V5/* lvl29 */ = 14,
_V6/* a29 */ = function(_V7/* s1onM */){
  var _V8/* s1onN */ = new T(function(){
    return B(A1(_V7/* s1onM */,_V5/* Text.Read.Lex.lvl29 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_V4/* Text.Read.Lex.a28 */, function(_V9/* s1onO */){
    return E(_V8/* s1onN */);
  })));
},
_Va/* a30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_Vb/* lvl35 */ = 1,
_Vc/* a31 */ = function(_Vd/* s1onS */){
  var _Ve/* s1onT */ = new T(function(){
    return B(A1(_Vd/* s1onS */,_Vb/* Text.Read.Lex.lvl35 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Va/* Text.Read.Lex.a30 */, function(_Vf/* s1onU */){
    return E(_Ve/* s1onT */);
  })));
},
_Vg/* a32 */ = function(_Vh/* s1onY */){
  return new T1(1,B(_QX/* Text.ParserCombinators.ReadP.$wa */(_Vc/* Text.Read.Lex.a31 */, _V6/* Text.Read.Lex.a29 */, _Vh/* s1onY */)));
},
_Vi/* a33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_Vj/* lvl36 */ = 0,
_Vk/* a34 */ = function(_Vl/* s1oo1 */){
  var _Vm/* s1oo2 */ = new T(function(){
    return B(A1(_Vl/* s1oo1 */,_Vj/* Text.Read.Lex.lvl36 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Vi/* Text.Read.Lex.a33 */, function(_Vn/* s1oo3 */){
    return E(_Vm/* s1oo2 */);
  })));
},
_Vo/* a35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_Vp/* lvl34 */ = 2,
_Vq/* a36 */ = function(_Vr/* s1oo7 */){
  var _Vs/* s1oo8 */ = new T(function(){
    return B(A1(_Vr/* s1oo7 */,_Vp/* Text.Read.Lex.lvl34 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Vo/* Text.Read.Lex.a35 */, function(_Vt/* s1oo9 */){
    return E(_Vs/* s1oo8 */);
  })));
},
_Vu/* a37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_Vv/* lvl33 */ = 3,
_Vw/* a38 */ = function(_Vx/* s1ood */){
  var _Vy/* s1ooe */ = new T(function(){
    return B(A1(_Vx/* s1ood */,_Vv/* Text.Read.Lex.lvl33 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Vu/* Text.Read.Lex.a37 */, function(_Vz/* s1oof */){
    return E(_Vy/* s1ooe */);
  })));
},
_VA/* a39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_VB/* lvl32 */ = 4,
_VC/* a40 */ = function(_VD/* s1ooj */){
  var _VE/* s1ook */ = new T(function(){
    return B(A1(_VD/* s1ooj */,_VB/* Text.Read.Lex.lvl32 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_VA/* Text.Read.Lex.a39 */, function(_VF/* s1ool */){
    return E(_VE/* s1ook */);
  })));
},
_VG/* a41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_VH/* lvl31 */ = 5,
_VI/* a42 */ = function(_VJ/* s1oop */){
  var _VK/* s1ooq */ = new T(function(){
    return B(A1(_VJ/* s1oop */,_VH/* Text.Read.Lex.lvl31 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_VG/* Text.Read.Lex.a41 */, function(_VL/* s1oor */){
    return E(_VK/* s1ooq */);
  })));
},
_VM/* a43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_VN/* lvl30 */ = 6,
_VO/* a44 */ = function(_VP/* s1oov */){
  var _VQ/* s1oow */ = new T(function(){
    return B(A1(_VP/* s1oov */,_VN/* Text.Read.Lex.lvl30 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_VM/* Text.Read.Lex.a43 */, function(_VR/* s1oox */){
    return E(_VQ/* s1oow */);
  })));
},
_VS/* a45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_VT/* lvl7 */ = 7,
_VU/* a46 */ = function(_VV/* s1ooB */){
  var _VW/* s1ooC */ = new T(function(){
    return B(A1(_VV/* s1ooB */,_VT/* Text.Read.Lex.lvl7 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_VS/* Text.Read.Lex.a45 */, function(_VX/* s1ooD */){
    return E(_VW/* s1ooC */);
  })));
},
_VY/* a47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_VZ/* lvl6 */ = 8,
_W0/* a48 */ = function(_W1/* s1ooH */){
  var _W2/* s1ooI */ = new T(function(){
    return B(A1(_W1/* s1ooH */,_VZ/* Text.Read.Lex.lvl6 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_VY/* Text.Read.Lex.a47 */, function(_W3/* s1ooJ */){
    return E(_W2/* s1ooI */);
  })));
},
_W4/* a49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_W5/* lvl2 */ = 9,
_W6/* a50 */ = function(_W7/* s1ooN */){
  var _W8/* s1ooO */ = new T(function(){
    return B(A1(_W7/* s1ooN */,_W5/* Text.Read.Lex.lvl2 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_W4/* Text.Read.Lex.a49 */, function(_W9/* s1ooP */){
    return E(_W8/* s1ooO */);
  })));
},
_Wa/* a51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_Wb/* lvl4 */ = 10,
_Wc/* a52 */ = function(_Wd/* s1ooT */){
  var _We/* s1ooU */ = new T(function(){
    return B(A1(_Wd/* s1ooT */,_Wb/* Text.Read.Lex.lvl4 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Wa/* Text.Read.Lex.a51 */, function(_Wf/* s1ooV */){
    return E(_We/* s1ooU */);
  })));
},
_Wg/* a53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_Wh/* lvl1 */ = 11,
_Wi/* a54 */ = function(_Wj/* s1ooZ */){
  var _Wk/* s1op0 */ = new T(function(){
    return B(A1(_Wj/* s1ooZ */,_Wh/* Text.Read.Lex.lvl1 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Wg/* Text.Read.Lex.a53 */, function(_Wl/* s1op1 */){
    return E(_Wk/* s1op0 */);
  })));
},
_Wm/* a55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_Wn/* lvl5 */ = 12,
_Wo/* a56 */ = function(_Wp/* s1op5 */){
  var _Wq/* s1op6 */ = new T(function(){
    return B(A1(_Wp/* s1op5 */,_Wn/* Text.Read.Lex.lvl5 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Wm/* Text.Read.Lex.a55 */, function(_Wr/* s1op7 */){
    return E(_Wq/* s1op6 */);
  })));
},
_Ws/* a57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_Wt/* lvl3 */ = 13,
_Wu/* a58 */ = function(_Wv/* s1opb */){
  var _Ww/* s1opc */ = new T(function(){
    return B(A1(_Wv/* s1opb */,_Wt/* Text.Read.Lex.lvl3 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Ws/* Text.Read.Lex.a57 */, function(_Wx/* s1opd */){
    return E(_Ww/* s1opc */);
  })));
},
_Wy/* a59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_Wz/* lvl28 */ = 15,
_WA/* a60 */ = function(_WB/* s1oph */){
  var _WC/* s1opi */ = new T(function(){
    return B(A1(_WB/* s1oph */,_Wz/* Text.Read.Lex.lvl28 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Wy/* Text.Read.Lex.a59 */, function(_WD/* s1opj */){
    return E(_WC/* s1opi */);
  })));
},
_WE/* a61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_WF/* lvl27 */ = 16,
_WG/* a62 */ = function(_WH/* s1opn */){
  var _WI/* s1opo */ = new T(function(){
    return B(A1(_WH/* s1opn */,_WF/* Text.Read.Lex.lvl27 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_WE/* Text.Read.Lex.a61 */, function(_WJ/* s1opp */){
    return E(_WI/* s1opo */);
  })));
},
_WK/* a63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_WL/* lvl26 */ = 17,
_WM/* a64 */ = function(_WN/* s1opt */){
  var _WO/* s1opu */ = new T(function(){
    return B(A1(_WN/* s1opt */,_WL/* Text.Read.Lex.lvl26 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_WK/* Text.Read.Lex.a63 */, function(_WP/* s1opv */){
    return E(_WO/* s1opu */);
  })));
},
_WQ/* a65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_WR/* lvl25 */ = 18,
_WS/* a66 */ = function(_WT/* s1opz */){
  var _WU/* s1opA */ = new T(function(){
    return B(A1(_WT/* s1opz */,_WR/* Text.Read.Lex.lvl25 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_WQ/* Text.Read.Lex.a65 */, function(_WV/* s1opB */){
    return E(_WU/* s1opA */);
  })));
},
_WW/* a67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_WX/* lvl24 */ = 19,
_WY/* a68 */ = function(_WZ/* s1opF */){
  var _X0/* s1opG */ = new T(function(){
    return B(A1(_WZ/* s1opF */,_WX/* Text.Read.Lex.lvl24 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_WW/* Text.Read.Lex.a67 */, function(_X1/* s1opH */){
    return E(_X0/* s1opG */);
  })));
},
_X2/* a69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_X3/* lvl23 */ = 20,
_X4/* a70 */ = function(_X5/* s1opL */){
  var _X6/* s1opM */ = new T(function(){
    return B(A1(_X5/* s1opL */,_X3/* Text.Read.Lex.lvl23 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_X2/* Text.Read.Lex.a69 */, function(_X7/* s1opN */){
    return E(_X6/* s1opM */);
  })));
},
_X8/* a71 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_X9/* lvl22 */ = 21,
_Xa/* a72 */ = function(_Xb/* s1opR */){
  var _Xc/* s1opS */ = new T(function(){
    return B(A1(_Xb/* s1opR */,_X9/* Text.Read.Lex.lvl22 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_X8/* Text.Read.Lex.a71 */, function(_Xd/* s1opT */){
    return E(_Xc/* s1opS */);
  })));
},
_Xe/* a73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_Xf/* lvl21 */ = 22,
_Xg/* a74 */ = function(_Xh/* s1opX */){
  var _Xi/* s1opY */ = new T(function(){
    return B(A1(_Xh/* s1opX */,_Xf/* Text.Read.Lex.lvl21 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Xe/* Text.Read.Lex.a73 */, function(_Xj/* s1opZ */){
    return E(_Xi/* s1opY */);
  })));
},
_Xk/* a75 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_Xl/* lvl20 */ = 23,
_Xm/* a76 */ = function(_Xn/* s1oq3 */){
  var _Xo/* s1oq4 */ = new T(function(){
    return B(A1(_Xn/* s1oq3 */,_Xl/* Text.Read.Lex.lvl20 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Xk/* Text.Read.Lex.a75 */, function(_Xp/* s1oq5 */){
    return E(_Xo/* s1oq4 */);
  })));
},
_Xq/* a77 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_Xr/* lvl19 */ = 24,
_Xs/* a78 */ = function(_Xt/* s1oq9 */){
  var _Xu/* s1oqa */ = new T(function(){
    return B(A1(_Xt/* s1oq9 */,_Xr/* Text.Read.Lex.lvl19 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Xq/* Text.Read.Lex.a77 */, function(_Xv/* s1oqb */){
    return E(_Xu/* s1oqa */);
  })));
},
_Xw/* a79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_Xx/* lvl18 */ = 25,
_Xy/* a80 */ = function(_Xz/* s1oqf */){
  var _XA/* s1oqg */ = new T(function(){
    return B(A1(_Xz/* s1oqf */,_Xx/* Text.Read.Lex.lvl18 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Xw/* Text.Read.Lex.a79 */, function(_XB/* s1oqh */){
    return E(_XA/* s1oqg */);
  })));
},
_XC/* a81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_XD/* lvl17 */ = 26,
_XE/* a82 */ = function(_XF/* s1oql */){
  var _XG/* s1oqm */ = new T(function(){
    return B(A1(_XF/* s1oql */,_XD/* Text.Read.Lex.lvl17 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_XC/* Text.Read.Lex.a81 */, function(_XH/* s1oqn */){
    return E(_XG/* s1oqm */);
  })));
},
_XI/* a83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_XJ/* lvl16 */ = 27,
_XK/* a84 */ = function(_XL/* s1oqr */){
  var _XM/* s1oqs */ = new T(function(){
    return B(A1(_XL/* s1oqr */,_XJ/* Text.Read.Lex.lvl16 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_XI/* Text.Read.Lex.a83 */, function(_XN/* s1oqt */){
    return E(_XM/* s1oqs */);
  })));
},
_XO/* a85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_XP/* lvl15 */ = 28,
_XQ/* a86 */ = function(_XR/* s1oqx */){
  var _XS/* s1oqy */ = new T(function(){
    return B(A1(_XR/* s1oqx */,_XP/* Text.Read.Lex.lvl15 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_XO/* Text.Read.Lex.a85 */, function(_XT/* s1oqz */){
    return E(_XS/* s1oqy */);
  })));
},
_XU/* a87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_XV/* lvl14 */ = 29,
_XW/* a88 */ = function(_XX/* s1oqD */){
  var _XY/* s1oqE */ = new T(function(){
    return B(A1(_XX/* s1oqD */,_XV/* Text.Read.Lex.lvl14 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_XU/* Text.Read.Lex.a87 */, function(_XZ/* s1oqF */){
    return E(_XY/* s1oqE */);
  })));
},
_Y0/* a89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_Y1/* lvl13 */ = 30,
_Y2/* a90 */ = function(_Y3/* s1oqJ */){
  var _Y4/* s1oqK */ = new T(function(){
    return B(A1(_Y3/* s1oqJ */,_Y1/* Text.Read.Lex.lvl13 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Y0/* Text.Read.Lex.a89 */, function(_Y5/* s1oqL */){
    return E(_Y4/* s1oqK */);
  })));
},
_Y6/* a91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_Y7/* lvl12 */ = 31,
_Y8/* a92 */ = function(_Y9/* s1oqP */){
  var _Ya/* s1oqQ */ = new T(function(){
    return B(A1(_Y9/* s1oqP */,_Y7/* Text.Read.Lex.lvl12 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Y6/* Text.Read.Lex.a91 */, function(_Yb/* s1oqR */){
    return E(_Ya/* s1oqQ */);
  })));
},
_Yc/* a93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_Yd/* x */ = 32,
_Ye/* a94 */ = function(_Yf/* s1oqV */){
  var _Yg/* s1oqW */ = new T(function(){
    return B(A1(_Yf/* s1oqV */,_Yd/* Text.Read.Lex.x */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Yc/* Text.Read.Lex.a93 */, function(_Yh/* s1oqX */){
    return E(_Yg/* s1oqW */);
  })));
},
_Yi/* a95 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DEL"));
}),
_Yj/* x1 */ = 127,
_Yk/* a96 */ = function(_Yl/* s1or1 */){
  var _Ym/* s1or2 */ = new T(function(){
    return B(A1(_Yl/* s1or1 */,_Yj/* Text.Read.Lex.x1 */));
  });
  return new T1(1,B(_US/* Text.ParserCombinators.ReadP.$wa6 */(_Yi/* Text.Read.Lex.a95 */, function(_Yn/* s1or3 */){
    return E(_Ym/* s1or2 */);
  })));
},
_Yo/* lvl47 */ = new T2(1,_Yk/* Text.Read.Lex.a96 */,_I/* GHC.Types.[] */),
_Yp/* lvl48 */ = new T2(1,_Ye/* Text.Read.Lex.a94 */,_Yo/* Text.Read.Lex.lvl47 */),
_Yq/* lvl49 */ = new T2(1,_Y8/* Text.Read.Lex.a92 */,_Yp/* Text.Read.Lex.lvl48 */),
_Yr/* lvl50 */ = new T2(1,_Y2/* Text.Read.Lex.a90 */,_Yq/* Text.Read.Lex.lvl49 */),
_Ys/* lvl51 */ = new T2(1,_XW/* Text.Read.Lex.a88 */,_Yr/* Text.Read.Lex.lvl50 */),
_Yt/* lvl52 */ = new T2(1,_XQ/* Text.Read.Lex.a86 */,_Ys/* Text.Read.Lex.lvl51 */),
_Yu/* lvl53 */ = new T2(1,_XK/* Text.Read.Lex.a84 */,_Yt/* Text.Read.Lex.lvl52 */),
_Yv/* lvl54 */ = new T2(1,_XE/* Text.Read.Lex.a82 */,_Yu/* Text.Read.Lex.lvl53 */),
_Yw/* lvl55 */ = new T2(1,_Xy/* Text.Read.Lex.a80 */,_Yv/* Text.Read.Lex.lvl54 */),
_Yx/* lvl56 */ = new T2(1,_Xs/* Text.Read.Lex.a78 */,_Yw/* Text.Read.Lex.lvl55 */),
_Yy/* lvl57 */ = new T2(1,_Xm/* Text.Read.Lex.a76 */,_Yx/* Text.Read.Lex.lvl56 */),
_Yz/* lvl58 */ = new T2(1,_Xg/* Text.Read.Lex.a74 */,_Yy/* Text.Read.Lex.lvl57 */),
_YA/* lvl59 */ = new T2(1,_Xa/* Text.Read.Lex.a72 */,_Yz/* Text.Read.Lex.lvl58 */),
_YB/* lvl60 */ = new T2(1,_X4/* Text.Read.Lex.a70 */,_YA/* Text.Read.Lex.lvl59 */),
_YC/* lvl61 */ = new T2(1,_WY/* Text.Read.Lex.a68 */,_YB/* Text.Read.Lex.lvl60 */),
_YD/* lvl62 */ = new T2(1,_WS/* Text.Read.Lex.a66 */,_YC/* Text.Read.Lex.lvl61 */),
_YE/* lvl63 */ = new T2(1,_WM/* Text.Read.Lex.a64 */,_YD/* Text.Read.Lex.lvl62 */),
_YF/* lvl64 */ = new T2(1,_WG/* Text.Read.Lex.a62 */,_YE/* Text.Read.Lex.lvl63 */),
_YG/* lvl65 */ = new T2(1,_WA/* Text.Read.Lex.a60 */,_YF/* Text.Read.Lex.lvl64 */),
_YH/* lvl66 */ = new T2(1,_Wu/* Text.Read.Lex.a58 */,_YG/* Text.Read.Lex.lvl65 */),
_YI/* lvl67 */ = new T2(1,_Wo/* Text.Read.Lex.a56 */,_YH/* Text.Read.Lex.lvl66 */),
_YJ/* lvl68 */ = new T2(1,_Wi/* Text.Read.Lex.a54 */,_YI/* Text.Read.Lex.lvl67 */),
_YK/* lvl69 */ = new T2(1,_Wc/* Text.Read.Lex.a52 */,_YJ/* Text.Read.Lex.lvl68 */),
_YL/* lvl70 */ = new T2(1,_W6/* Text.Read.Lex.a50 */,_YK/* Text.Read.Lex.lvl69 */),
_YM/* lvl71 */ = new T2(1,_W0/* Text.Read.Lex.a48 */,_YL/* Text.Read.Lex.lvl70 */),
_YN/* lvl72 */ = new T2(1,_VU/* Text.Read.Lex.a46 */,_YM/* Text.Read.Lex.lvl71 */),
_YO/* lvl73 */ = new T2(1,_VO/* Text.Read.Lex.a44 */,_YN/* Text.Read.Lex.lvl72 */),
_YP/* lvl74 */ = new T2(1,_VI/* Text.Read.Lex.a42 */,_YO/* Text.Read.Lex.lvl73 */),
_YQ/* lvl75 */ = new T2(1,_VC/* Text.Read.Lex.a40 */,_YP/* Text.Read.Lex.lvl74 */),
_YR/* lvl76 */ = new T2(1,_Vw/* Text.Read.Lex.a38 */,_YQ/* Text.Read.Lex.lvl75 */),
_YS/* lvl77 */ = new T2(1,_Vq/* Text.Read.Lex.a36 */,_YR/* Text.Read.Lex.lvl76 */),
_YT/* lvl78 */ = new T2(1,_Vk/* Text.Read.Lex.a34 */,_YS/* Text.Read.Lex.lvl77 */),
_YU/* lvl79 */ = new T2(1,_Vg/* Text.Read.Lex.a32 */,_YT/* Text.Read.Lex.lvl78 */),
_YV/* lexAscii */ = new T(function(){
  return B(_UK/* Text.ParserCombinators.ReadP.choice */(_YU/* Text.Read.Lex.lvl79 */));
}),
_YW/* lvl10 */ = 34,
_YX/* lvl11 */ = new T1(0,1114111),
_YY/* lvl8 */ = 92,
_YZ/* lvl9 */ = 39,
_Z0/* lexChar2 */ = function(_Z1/* s1or7 */){
  var _Z2/* s1or8 */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_VT/* Text.Read.Lex.lvl7 */));
  }),
  _Z3/* s1or9 */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_VZ/* Text.Read.Lex.lvl6 */));
  }),
  _Z4/* s1ora */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_W5/* Text.Read.Lex.lvl2 */));
  }),
  _Z5/* s1orb */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_Wb/* Text.Read.Lex.lvl4 */));
  }),
  _Z6/* s1orc */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_Wh/* Text.Read.Lex.lvl1 */));
  }),
  _Z7/* s1ord */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_Wn/* Text.Read.Lex.lvl5 */));
  }),
  _Z8/* s1ore */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_Wt/* Text.Read.Lex.lvl3 */));
  }),
  _Z9/* s1orf */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_YY/* Text.Read.Lex.lvl8 */));
  }),
  _Za/* s1org */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_YZ/* Text.Read.Lex.lvl9 */));
  }),
  _Zb/* s1orh */ = new T(function(){
    return B(A1(_Z1/* s1or7 */,_YW/* Text.Read.Lex.lvl10 */));
  }),
  _Zc/* s1osl */ = new T(function(){
    var _Zd/* s1orE */ = function(_Ze/* s1oro */){
      var _Zf/* s1orp */ = new T(function(){
        return B(_T2/* GHC.Integer.Type.smallInteger */(E(_Ze/* s1oro */)));
      }),
      _Zg/* s1orB */ = function(_Zh/* s1ors */){
        var _Zi/* s1ort */ = B(_TD/* Text.Read.Lex.valInteger */(_Zf/* s1orp */, _Zh/* s1ors */));
        if(!B(_UA/* GHC.Integer.Type.leInteger */(_Zi/* s1ort */, _YX/* Text.Read.Lex.lvl11 */))){
          return new T0(2);
        }else{
          return new F(function(){return A1(_Z1/* s1or7 */,new T(function(){
            var _Zj/* s1orv */ = B(_Ux/* GHC.Integer.Type.integerToInt */(_Zi/* s1ort */));
            if(_Zj/* s1orv */>>>0>1114111){
              return B(_Uv/* GHC.Char.chr2 */(_Zj/* s1orv */));
            }else{
              return _Zj/* s1orv */;
            }
          }));});
        }
      };
      return new T1(1,B(_RE/* Text.Read.Lex.$wa6 */(_Ze/* s1oro */, _Zg/* s1orB */)));
    },
    _Zk/* s1osk */ = new T(function(){
      var _Zl/* s1orI */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Y7/* Text.Read.Lex.lvl12 */));
      }),
      _Zm/* s1orJ */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Y1/* Text.Read.Lex.lvl13 */));
      }),
      _Zn/* s1orK */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_XV/* Text.Read.Lex.lvl14 */));
      }),
      _Zo/* s1orL */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_XP/* Text.Read.Lex.lvl15 */));
      }),
      _Zp/* s1orM */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_XJ/* Text.Read.Lex.lvl16 */));
      }),
      _Zq/* s1orN */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_XD/* Text.Read.Lex.lvl17 */));
      }),
      _Zr/* s1orO */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Xx/* Text.Read.Lex.lvl18 */));
      }),
      _Zs/* s1orP */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Xr/* Text.Read.Lex.lvl19 */));
      }),
      _Zt/* s1orQ */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Xl/* Text.Read.Lex.lvl20 */));
      }),
      _Zu/* s1orR */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Xf/* Text.Read.Lex.lvl21 */));
      }),
      _Zv/* s1orS */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_X9/* Text.Read.Lex.lvl22 */));
      }),
      _Zw/* s1orT */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_X3/* Text.Read.Lex.lvl23 */));
      }),
      _Zx/* s1orU */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_WX/* Text.Read.Lex.lvl24 */));
      }),
      _Zy/* s1orV */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_WR/* Text.Read.Lex.lvl25 */));
      }),
      _Zz/* s1orW */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_WL/* Text.Read.Lex.lvl26 */));
      }),
      _ZA/* s1orX */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_WF/* Text.Read.Lex.lvl27 */));
      }),
      _ZB/* s1orY */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Wz/* Text.Read.Lex.lvl28 */));
      }),
      _ZC/* s1orZ */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_V5/* Text.Read.Lex.lvl29 */));
      }),
      _ZD/* s1os0 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_VN/* Text.Read.Lex.lvl30 */));
      }),
      _ZE/* s1os1 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_VH/* Text.Read.Lex.lvl31 */));
      }),
      _ZF/* s1os2 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_VB/* Text.Read.Lex.lvl32 */));
      }),
      _ZG/* s1os3 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Vv/* Text.Read.Lex.lvl33 */));
      }),
      _ZH/* s1os4 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Vp/* Text.Read.Lex.lvl34 */));
      }),
      _ZI/* s1os5 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Vb/* Text.Read.Lex.lvl35 */));
      }),
      _ZJ/* s1os6 */ = new T(function(){
        return B(A1(_Z1/* s1or7 */,_Vj/* Text.Read.Lex.lvl36 */));
      }),
      _ZK/* s1os7 */ = function(_ZL/* s1os8 */){
        switch(E(_ZL/* s1os8 */)){
          case 64:
            return E(_ZJ/* s1os6 */);
          case 65:
            return E(_ZI/* s1os5 */);
          case 66:
            return E(_ZH/* s1os4 */);
          case 67:
            return E(_ZG/* s1os3 */);
          case 68:
            return E(_ZF/* s1os2 */);
          case 69:
            return E(_ZE/* s1os1 */);
          case 70:
            return E(_ZD/* s1os0 */);
          case 71:
            return E(_Z2/* s1or8 */);
          case 72:
            return E(_Z3/* s1or9 */);
          case 73:
            return E(_Z4/* s1ora */);
          case 74:
            return E(_Z5/* s1orb */);
          case 75:
            return E(_Z6/* s1orc */);
          case 76:
            return E(_Z7/* s1ord */);
          case 77:
            return E(_Z8/* s1ore */);
          case 78:
            return E(_ZC/* s1orZ */);
          case 79:
            return E(_ZB/* s1orY */);
          case 80:
            return E(_ZA/* s1orX */);
          case 81:
            return E(_Zz/* s1orW */);
          case 82:
            return E(_Zy/* s1orV */);
          case 83:
            return E(_Zx/* s1orU */);
          case 84:
            return E(_Zw/* s1orT */);
          case 85:
            return E(_Zv/* s1orS */);
          case 86:
            return E(_Zu/* s1orR */);
          case 87:
            return E(_Zt/* s1orQ */);
          case 88:
            return E(_Zs/* s1orP */);
          case 89:
            return E(_Zr/* s1orO */);
          case 90:
            return E(_Zq/* s1orN */);
          case 91:
            return E(_Zp/* s1orM */);
          case 92:
            return E(_Zo/* s1orL */);
          case 93:
            return E(_Zn/* s1orK */);
          case 94:
            return E(_Zm/* s1orJ */);
          case 95:
            return E(_Zl/* s1orI */);
          default:
            return new T0(2);
        }
      };
      return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_ZM/* s1osd */){
        return (E(_ZM/* s1osd */)==94) ? E(new T1(0,_ZK/* s1os7 */)) : new T0(2);
      }), new T(function(){
        return B(A1(_YV/* Text.Read.Lex.lexAscii */,_Z1/* s1or7 */));
      })));
    });
    return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_QX/* Text.ParserCombinators.ReadP.$wa */(_Ur/* Text.Read.Lex.a4 */, _Ut/* Text.Read.Lex.a5 */, _Zd/* s1orE */))), _Zk/* s1osk */));
  });
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_ZN/* s1ori */){
    switch(E(_ZN/* s1ori */)){
      case 34:
        return E(_Zb/* s1orh */);
      case 39:
        return E(_Za/* s1org */);
      case 92:
        return E(_Z9/* s1orf */);
      case 97:
        return E(_Z2/* s1or8 */);
      case 98:
        return E(_Z3/* s1or9 */);
      case 102:
        return E(_Z7/* s1ord */);
      case 110:
        return E(_Z5/* s1orb */);
      case 114:
        return E(_Z8/* s1ore */);
      case 116:
        return E(_Z4/* s1ora */);
      case 118:
        return E(_Z6/* s1orc */);
      default:
        return new T0(2);
    }
  }), _Zc/* s1osl */);});
},
_ZO/* a */ = function(_ZP/* s1iyn */){
  return new F(function(){return A1(_ZP/* s1iyn */,_0/* GHC.Tuple.() */);});
},
_ZQ/* skipSpaces_skip */ = function(_ZR/* s1iIB */){
  var _ZS/* s1iIC */ = E(_ZR/* s1iIB */);
  if(!_ZS/* s1iIC */._){
    return E(_ZO/* Text.ParserCombinators.ReadP.a */);
  }else{
    var _ZT/* s1iIF */ = E(_ZS/* s1iIC */.a),
    _ZU/* s1iIH */ = _ZT/* s1iIF */>>>0,
    _ZV/* s1iIJ */ = new T(function(){
      return B(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */(_ZS/* s1iIC */.b));
    });
    if(_ZU/* s1iIH */>887){
      var _ZW/* s1iIO */ = u_iswspace/* EXTERNAL */(_ZT/* s1iIF */);
      if(!E(_ZW/* s1iIO */)){
        return E(_ZO/* Text.ParserCombinators.ReadP.a */);
      }else{
        var _ZX/* s1iIW */ = function(_ZY/* s1iIS */){
          var _ZZ/* s1iIT */ = new T(function(){
            return B(A1(_ZV/* s1iIJ */,_ZY/* s1iIS */));
          });
          return new T1(0,function(_100/* s1iIU */){
            return E(_ZZ/* s1iIT */);
          });
        };
        return E(_ZX/* s1iIW */);
      }
    }else{
      var _101/* s1iIX */ = E(_ZU/* s1iIH */);
      if(_101/* s1iIX */==32){
        var _102/* s1iJg */ = function(_103/* s1iJc */){
          var _104/* s1iJd */ = new T(function(){
            return B(A1(_ZV/* s1iIJ */,_103/* s1iJc */));
          });
          return new T1(0,function(_105/* s1iJe */){
            return E(_104/* s1iJd */);
          });
        };
        return E(_102/* s1iJg */);
      }else{
        if(_101/* s1iIX */-9>>>0>4){
          if(E(_101/* s1iIX */)==160){
            var _106/* s1iJ6 */ = function(_107/* s1iJ2 */){
              var _108/* s1iJ3 */ = new T(function(){
                return B(A1(_ZV/* s1iIJ */,_107/* s1iJ2 */));
              });
              return new T1(0,function(_109/* s1iJ4 */){
                return E(_108/* s1iJ3 */);
              });
            };
            return E(_106/* s1iJ6 */);
          }else{
            return E(_ZO/* Text.ParserCombinators.ReadP.a */);
          }
        }else{
          var _10a/* s1iJb */ = function(_10b/* s1iJ7 */){
            var _10c/* s1iJ8 */ = new T(function(){
              return B(A1(_ZV/* s1iIJ */,_10b/* s1iJ7 */));
            });
            return new T1(0,function(_10d/* s1iJ9 */){
              return E(_10c/* s1iJ8 */);
            });
          };
          return E(_10a/* s1iJb */);
        }
      }
    }
  }
},
_10e/* a97 */ = function(_10f/* s1osm */){
  var _10g/* s1osn */ = new T(function(){
    return B(_10e/* Text.Read.Lex.a97 */(_10f/* s1osm */));
  }),
  _10h/* s1oso */ = function(_10i/* s1osp */){
    return (E(_10i/* s1osp */)==92) ? E(_10g/* s1osn */) : new T0(2);
  },
  _10j/* s1osu */ = function(_10k/* s1osv */){
    return E(new T1(0,_10h/* s1oso */));
  },
  _10l/* s1osy */ = new T1(1,function(_10m/* s1osx */){
    return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_10m/* s1osx */, _10j/* s1osu */);});
  }),
  _10n/* s1osz */ = new T(function(){
    return B(_Z0/* Text.Read.Lex.lexChar2 */(function(_10o/* s1osA */){
      return new F(function(){return A1(_10f/* s1osm */,new T2(0,_10o/* s1osA */,_8g/* GHC.Types.True */));});
    }));
  }),
  _10p/* s1osD */ = function(_10q/* s1osE */){
    var _10r/* s1osH */ = E(_10q/* s1osE */);
    if(_10r/* s1osH */==38){
      return E(_10g/* s1osn */);
    }else{
      var _10s/* s1osI */ = _10r/* s1osH */>>>0;
      if(_10s/* s1osI */>887){
        var _10t/* s1osO */ = u_iswspace/* EXTERNAL */(_10r/* s1osH */);
        return (E(_10t/* s1osO */)==0) ? new T0(2) : E(_10l/* s1osy */);
      }else{
        var _10u/* s1osS */ = E(_10s/* s1osI */);
        return (_10u/* s1osS */==32) ? E(_10l/* s1osy */) : (_10u/* s1osS */-9>>>0>4) ? (E(_10u/* s1osS */)==160) ? E(_10l/* s1osy */) : new T0(2) : E(_10l/* s1osy */);
      }
    }
  };
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_10v/* s1osY */){
    return (E(_10v/* s1osY */)==92) ? E(new T1(0,_10p/* s1osD */)) : new T0(2);
  }), new T1(0,function(_10w/* s1ot4 */){
    var _10x/* s1ot5 */ = E(_10w/* s1ot4 */);
    if(E(_10x/* s1ot5 */)==92){
      return E(_10n/* s1osz */);
    }else{
      return new F(function(){return A1(_10f/* s1osm */,new T2(0,_10x/* s1ot5 */,_2G/* GHC.Types.False */));});
    }
  }));});
},
_10y/* a98 */ = function(_10z/* s1otb */, _10A/* s1otc */){
  var _10B/* s1otd */ = new T(function(){
    return B(A1(_10A/* s1otc */,new T1(1,new T(function(){
      return B(A1(_10z/* s1otb */,_I/* GHC.Types.[] */));
    }))));
  }),
  _10C/* s1otu */ = function(_10D/* s1otg */){
    var _10E/* s1oth */ = E(_10D/* s1otg */),
    _10F/* s1otk */ = E(_10E/* s1oth */.a);
    if(E(_10F/* s1otk */)==34){
      if(!E(_10E/* s1oth */.b)){
        return E(_10B/* s1otd */);
      }else{
        return new F(function(){return _10y/* Text.Read.Lex.a98 */(function(_10G/* s1otr */){
          return new F(function(){return A1(_10z/* s1otb */,new T2(1,_10F/* s1otk */,_10G/* s1otr */));});
        }, _10A/* s1otc */);});
      }
    }else{
      return new F(function(){return _10y/* Text.Read.Lex.a98 */(function(_10H/* s1otn */){
        return new F(function(){return A1(_10z/* s1otb */,new T2(1,_10F/* s1otk */,_10H/* s1otn */));});
      }, _10A/* s1otc */);});
    }
  };
  return new F(function(){return _10e/* Text.Read.Lex.a97 */(_10C/* s1otu */);});
},
_10I/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_\'"));
}),
_10J/* $wisIdfChar */ = function(_10K/* s1otE */){
  var _10L/* s1otH */ = u_iswalnum/* EXTERNAL */(_10K/* s1otE */);
  if(!E(_10L/* s1otH */)){
    return new F(function(){return _Ue/* GHC.List.elem */(_Qt/* GHC.Classes.$fEqChar */, _10K/* s1otE */, _10I/* Text.Read.Lex.lvl45 */);});
  }else{
    return true;
  }
},
_10M/* isIdfChar */ = function(_10N/* s1otM */){
  return new F(function(){return _10J/* Text.Read.Lex.$wisIdfChar */(E(_10N/* s1otM */));});
},
_10O/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(",;()[]{}`"));
}),
_10P/* a7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("=>"));
}),
_10Q/* a8 */ = new T2(1,_10P/* Text.Read.Lex.a7 */,_I/* GHC.Types.[] */),
_10R/* a9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("~"));
}),
_10S/* a10 */ = new T2(1,_10R/* Text.Read.Lex.a9 */,_10Q/* Text.Read.Lex.a8 */),
_10T/* a11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("@"));
}),
_10U/* a12 */ = new T2(1,_10T/* Text.Read.Lex.a11 */,_10S/* Text.Read.Lex.a10 */),
_10V/* a13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("->"));
}),
_10W/* a14 */ = new T2(1,_10V/* Text.Read.Lex.a13 */,_10U/* Text.Read.Lex.a12 */),
_10X/* a15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<-"));
}),
_10Y/* a16 */ = new T2(1,_10X/* Text.Read.Lex.a15 */,_10W/* Text.Read.Lex.a14 */),
_10Z/* a17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("|"));
}),
_110/* a18 */ = new T2(1,_10Z/* Text.Read.Lex.a17 */,_10Y/* Text.Read.Lex.a16 */),
_111/* a19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\"));
}),
_112/* a20 */ = new T2(1,_111/* Text.Read.Lex.a19 */,_110/* Text.Read.Lex.a18 */),
_113/* a21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_114/* a22 */ = new T2(1,_113/* Text.Read.Lex.a21 */,_112/* Text.Read.Lex.a20 */),
_115/* a23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("::"));
}),
_116/* a24 */ = new T2(1,_115/* Text.Read.Lex.a23 */,_114/* Text.Read.Lex.a22 */),
_117/* a25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".."));
}),
_118/* reserved_ops */ = new T2(1,_117/* Text.Read.Lex.a25 */,_116/* Text.Read.Lex.a24 */),
_119/* expect2 */ = function(_11a/* s1otP */){
  var _11b/* s1otQ */ = new T(function(){
    return B(A1(_11a/* s1otP */,_RB/* Text.Read.Lex.EOF */));
  }),
  _11c/* s1ovk */ = new T(function(){
    var _11d/* s1otX */ = new T(function(){
      var _11e/* s1ou6 */ = function(_11f/* s1otY */){
        var _11g/* s1otZ */ = new T(function(){
          return B(A1(_11a/* s1otP */,new T1(0,_11f/* s1otY */)));
        });
        return new T1(0,function(_11h/* s1ou1 */){
          return (E(_11h/* s1ou1 */)==39) ? E(_11g/* s1otZ */) : new T0(2);
        });
      };
      return B(_Z0/* Text.Read.Lex.lexChar2 */(_11e/* s1ou6 */));
    }),
    _11i/* s1ou7 */ = function(_11j/* s1ou8 */){
      var _11k/* s1ou9 */ = E(_11j/* s1ou8 */);
      switch(E(_11k/* s1ou9 */)){
        case 39:
          return new T0(2);
        case 92:
          return E(_11d/* s1otX */);
        default:
          var _11l/* s1ouc */ = new T(function(){
            return B(A1(_11a/* s1otP */,new T1(0,_11k/* s1ou9 */)));
          });
          return new T1(0,function(_11m/* s1oue */){
            return (E(_11m/* s1oue */)==39) ? E(_11l/* s1ouc */) : new T0(2);
          });
      }
    },
    _11n/* s1ovj */ = new T(function(){
      var _11o/* s1ouq */ = new T(function(){
        return B(_10y/* Text.Read.Lex.a98 */(_4/* GHC.Base.id */, _11a/* s1otP */));
      }),
      _11p/* s1ovi */ = new T(function(){
        var _11q/* s1ovh */ = new T(function(){
          var _11r/* s1ovg */ = new T(function(){
            var _11s/* s1ovb */ = function(_11t/* s1ouP */){
              var _11u/* s1ouQ */ = E(_11t/* s1ouP */),
              _11v/* s1ouU */ = u_iswalpha/* EXTERNAL */(_11u/* s1ouQ */);
              return (E(_11v/* s1ouU */)==0) ? (E(_11u/* s1ouQ */)==95) ? new T1(1,B(_Rn/* Text.ParserCombinators.ReadP.$wa3 */(_10M/* Text.Read.Lex.isIdfChar */, function(_11w/* s1ov5 */){
                return new F(function(){return A1(_11a/* s1otP */,new T1(3,new T2(1,_11u/* s1ouQ */,_11w/* s1ov5 */)));});
              }))) : new T0(2) : new T1(1,B(_Rn/* Text.ParserCombinators.ReadP.$wa3 */(_10M/* Text.Read.Lex.isIdfChar */, function(_11x/* s1ouY */){
                return new F(function(){return A1(_11a/* s1otP */,new T1(3,new T2(1,_11u/* s1ouQ */,_11x/* s1ouY */)));});
              })));
            };
            return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_11s/* s1ovb */), new T(function(){
              return new T1(1,B(_QX/* Text.ParserCombinators.ReadP.$wa */(_Sz/* Text.Read.Lex.a2 */, _Ua/* Text.Read.Lex.a27 */, _11a/* s1otP */)));
            })));
          }),
          _11y/* s1ouN */ = function(_11z/* s1ouD */){
            return (!B(_Ue/* GHC.List.elem */(_Qt/* GHC.Classes.$fEqChar */, _11z/* s1ouD */, _Uj/* Text.Read.Lex.lvl44 */))) ? new T0(2) : new T1(1,B(_Rn/* Text.ParserCombinators.ReadP.$wa3 */(_Uk/* Text.Read.Lex.a6 */, function(_11A/* s1ouF */){
              var _11B/* s1ouG */ = new T2(1,_11z/* s1ouD */,_11A/* s1ouF */);
              if(!B(_Ue/* GHC.List.elem */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, _11B/* s1ouG */, _118/* Text.Read.Lex.reserved_ops */))){
                return new F(function(){return A1(_11a/* s1otP */,new T1(4,_11B/* s1ouG */));});
              }else{
                return new F(function(){return A1(_11a/* s1otP */,new T1(2,_11B/* s1ouG */));});
              }
            })));
          };
          return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_11y/* s1ouN */), _11r/* s1ovg */));
        });
        return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11C/* s1oux */){
          if(!B(_Ue/* GHC.List.elem */(_Qt/* GHC.Classes.$fEqChar */, _11C/* s1oux */, _10O/* Text.Read.Lex.lvl43 */))){
            return new T0(2);
          }else{
            return new F(function(){return A1(_11a/* s1otP */,new T1(2,new T2(1,_11C/* s1oux */,_I/* GHC.Types.[] */)));});
          }
        }), _11q/* s1ovh */));
      });
      return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11D/* s1our */){
        return (E(_11D/* s1our */)==34) ? E(_11o/* s1ouq */) : new T0(2);
      }), _11p/* s1ovi */));
    });
    return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11E/* s1ouk */){
      return (E(_11E/* s1ouk */)==39) ? E(new T1(0,_11i/* s1ou7 */)) : new T0(2);
    }), _11n/* s1ovj */));
  });
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_11F/* s1otR */){
    return (E(_11F/* s1otR */)._==0) ? E(_11b/* s1otQ */) : new T0(2);
  }), _11c/* s1ovk */);});
},
_11G/* minPrec */ = 0,
_11H/* $wa3 */ = function(_11I/* s1viS */, _11J/* s1viT */){
  var _11K/* s1viU */ = new T(function(){
    var _11L/* s1viV */ = new T(function(){
      var _11M/* s1vj8 */ = function(_11N/* s1viW */){
        var _11O/* s1viX */ = new T(function(){
          var _11P/* s1viY */ = new T(function(){
            return B(A1(_11J/* s1viT */,_11N/* s1viW */));
          });
          return B(_119/* Text.Read.Lex.expect2 */(function(_11Q/* s1viZ */){
            var _11R/* s1vj0 */ = E(_11Q/* s1viZ */);
            return (_11R/* s1vj0 */._==2) ? (!B(_IO/* GHC.Base.eqString */(_11R/* s1vj0 */.a, _Qm/* GHC.Read.$fRead(,)4 */))) ? new T0(2) : E(_11P/* s1viY */) : new T0(2);
          }));
        }),
        _11S/* s1vj4 */ = function(_11T/* s1vj5 */){
          return E(_11O/* s1viX */);
        };
        return new T1(1,function(_11U/* s1vj6 */){
          return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_11U/* s1vj6 */, _11S/* s1vj4 */);});
        });
      };
      return B(A2(_11I/* s1viS */,_11G/* Text.ParserCombinators.ReadPrec.minPrec */, _11M/* s1vj8 */));
    });
    return B(_119/* Text.Read.Lex.expect2 */(function(_11V/* s1vj9 */){
      var _11W/* s1vja */ = E(_11V/* s1vj9 */);
      return (_11W/* s1vja */._==2) ? (!B(_IO/* GHC.Base.eqString */(_11W/* s1vja */.a, _Ql/* GHC.Read.$fRead(,)3 */))) ? new T0(2) : E(_11L/* s1viV */) : new T0(2);
    }));
  }),
  _11X/* s1vje */ = function(_11Y/* s1vjf */){
    return E(_11K/* s1viU */);
  };
  return function(_11Z/* s1vjg */){
    return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_11Z/* s1vjg */, _11X/* s1vje */);});
  };
},
_120/* $fReadDouble10 */ = function(_121/* s1vjn */, _122/* s1vjo */){
  var _123/* s1vjp */ = function(_124/* s1vjq */){
    var _125/* s1vjr */ = new T(function(){
      return B(A1(_121/* s1vjn */,_124/* s1vjq */));
    }),
    _126/* s1vjx */ = function(_127/* s1vjs */){
      return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_125/* s1vjr */,_127/* s1vjs */)), new T(function(){
        return new T1(1,B(_11H/* GHC.Read.$wa3 */(_123/* s1vjp */, _127/* s1vjs */)));
      }));});
    };
    return E(_126/* s1vjx */);
  },
  _128/* s1vjy */ = new T(function(){
    return B(A1(_121/* s1vjn */,_122/* s1vjo */));
  }),
  _129/* s1vjE */ = function(_12a/* s1vjz */){
    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_128/* s1vjy */,_12a/* s1vjz */)), new T(function(){
      return new T1(1,B(_11H/* GHC.Read.$wa3 */(_123/* s1vjp */, _12a/* s1vjz */)));
    }));});
  };
  return E(_129/* s1vjE */);
},
_12b/* $fReadInt3 */ = function(_12c/* s1vlT */, _12d/* s1vlU */){
  var _12e/* s1vmt */ = function(_12f/* s1vlV */, _12g/* s1vlW */){
    var _12h/* s1vlX */ = function(_12i/* s1vlY */){
      return new F(function(){return A1(_12g/* s1vlW */,new T(function(){
        return  -E(_12i/* s1vlY */);
      }));});
    },
    _12j/* s1vm5 */ = new T(function(){
      return B(_119/* Text.Read.Lex.expect2 */(function(_12k/* s1vm4 */){
        return new F(function(){return A3(_12c/* s1vlT */,_12k/* s1vm4 */, _12f/* s1vlV */, _12h/* s1vlX */);});
      }));
    }),
    _12l/* s1vm6 */ = function(_12m/* s1vm7 */){
      return E(_12j/* s1vm5 */);
    },
    _12n/* s1vm8 */ = function(_12o/* s1vm9 */){
      return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12o/* s1vm9 */, _12l/* s1vm6 */);});
    },
    _12p/* s1vmo */ = new T(function(){
      return B(_119/* Text.Read.Lex.expect2 */(function(_12q/* s1vmc */){
        var _12r/* s1vmd */ = E(_12q/* s1vmc */);
        if(_12r/* s1vmd */._==4){
          var _12s/* s1vmf */ = E(_12r/* s1vmd */.a);
          if(!_12s/* s1vmf */._){
            return new F(function(){return A3(_12c/* s1vlT */,_12r/* s1vmd */, _12f/* s1vlV */, _12g/* s1vlW */);});
          }else{
            if(E(_12s/* s1vmf */.a)==45){
              if(!E(_12s/* s1vmf */.b)._){
                return E(new T1(1,_12n/* s1vm8 */));
              }else{
                return new F(function(){return A3(_12c/* s1vlT */,_12r/* s1vmd */, _12f/* s1vlV */, _12g/* s1vlW */);});
              }
            }else{
              return new F(function(){return A3(_12c/* s1vlT */,_12r/* s1vmd */, _12f/* s1vlV */, _12g/* s1vlW */);});
            }
          }
        }else{
          return new F(function(){return A3(_12c/* s1vlT */,_12r/* s1vmd */, _12f/* s1vlV */, _12g/* s1vlW */);});
        }
      }));
    }),
    _12t/* s1vmp */ = function(_12u/* s1vmq */){
      return E(_12p/* s1vmo */);
    };
    return new T1(1,function(_12v/* s1vmr */){
      return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12v/* s1vmr */, _12t/* s1vmp */);});
    });
  };
  return new F(function(){return _120/* GHC.Read.$fReadDouble10 */(_12e/* s1vmt */, _12d/* s1vlU */);});
},
_12w/* numberToInteger */ = function(_12x/* s1ojv */){
  var _12y/* s1ojw */ = E(_12x/* s1ojv */);
  if(!_12y/* s1ojw */._){
    var _12z/* s1ojy */ = _12y/* s1ojw */.b,
    _12A/* s1ojF */ = new T(function(){
      return B(_Tm/* Text.Read.Lex.numberToFixed_go */(new T(function(){
        return B(_T2/* GHC.Integer.Type.smallInteger */(E(_12y/* s1ojw */.a)));
      }), new T(function(){
        return B(_SX/* GHC.List.$wlenAcc */(_12z/* s1ojy */, 0));
      },1), B(_2S/* GHC.Base.map */(_T4/* Text.Read.Lex.numberToFixed2 */, _12z/* s1ojy */))));
    });
    return new T1(1,_12A/* s1ojF */);
  }else{
    return (E(_12y/* s1ojw */.b)._==0) ? (E(_12y/* s1ojw */.c)._==0) ? new T1(1,new T(function(){
      return B(_TD/* Text.Read.Lex.valInteger */(_SW/* Text.Read.Lex.numberToFixed1 */, _12y/* s1ojw */.a));
    })) : __Z/* EXTERNAL */ : __Z/* EXTERNAL */;
  }
},
_12B/* pfail1 */ = function(_12C/* s1kH8 */, _12D/* s1kH9 */){
  return new T0(2);
},
_12E/* $fReadInt_$sconvertInt */ = function(_12F/* s1vie */){
  var _12G/* s1vif */ = E(_12F/* s1vie */);
  if(_12G/* s1vif */._==5){
    var _12H/* s1vih */ = B(_12w/* Text.Read.Lex.numberToInteger */(_12G/* s1vif */.a));
    if(!_12H/* s1vih */._){
      return E(_12B/* Text.ParserCombinators.ReadPrec.pfail1 */);
    }else{
      var _12I/* s1vij */ = new T(function(){
        return B(_Ux/* GHC.Integer.Type.integerToInt */(_12H/* s1vih */.a));
      });
      return function(_12J/* s1vil */, _12K/* s1vim */){
        return new F(function(){return A1(_12K/* s1vim */,_12I/* s1vij */);});
      };
    }
  }else{
    return E(_12B/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_12L/* readEither5 */ = function(_12M/* s2Rfe */){
  var _12N/* s2Rfg */ = function(_12O/* s2Rfh */){
    return E(new T2(3,_12M/* s2Rfe */,_QO/* Text.ParserCombinators.ReadP.Fail */));
  };
  return new T1(1,function(_12P/* s2Rfi */){
    return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12P/* s2Rfi */, _12N/* s2Rfg */);});
  });
},
_12Q/* updateElementValue1 */ = new T(function(){
  return B(A3(_12b/* GHC.Read.$fReadInt3 */,_12E/* GHC.Read.$fReadInt_$sconvertInt */, _11G/* Text.ParserCombinators.ReadPrec.minPrec */, _12L/* Text.Read.readEither5 */));
}),
_12R/* updateElementValue */ = function(_12S/* s6AO */, _12T/* s6AP */){
  var _12U/* s6AQ */ = E(_12S/* s6AO */);
  switch(_12U/* s6AQ */._){
    case 1:
      return new T3(1,_12U/* s6AQ */.a,_12T/* s6AP */,_12U/* s6AQ */.c);
    case 2:
      return new T3(2,_12U/* s6AQ */.a,_12T/* s6AP */,_12U/* s6AQ */.c);
    case 3:
      return new T3(3,_12U/* s6AQ */.a,_12T/* s6AP */,_12U/* s6AQ */.c);
    case 4:
      return new T4(4,_12U/* s6AQ */.a,new T(function(){
        var _12V/* s6B5 */ = B(_Os/* Text.Read.readEither6 */(B(_Oz/* Text.ParserCombinators.ReadP.run */(_12Q/* FormEngine.FormElement.Updating.updateElementValue1 */, _12T/* s6AP */))));
        if(!_12V/* s6B5 */._){
          return __Z/* EXTERNAL */;
        }else{
          if(!E(_12V/* s6B5 */.b)._){
            return new T1(1,_12V/* s6B5 */.a);
          }else{
            return __Z/* EXTERNAL */;
          }
        }
      }),_12U/* s6AQ */.c,_12U/* s6AQ */.d);
    case 5:
      var _12W/* s6BB */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_12X/* s6Bf */){
          var _12Y/* s6Bg */ = E(_12X/* s6Bf */);
          if(!_12Y/* s6Bg */._){
            var _12Z/* s6Bj */ = E(_12Y/* s6Bg */.a);
            return (_12Z/* s6Bj */._==0) ? (!B(_IO/* GHC.Base.eqString */(_12Z/* s6Bj */.a, _12T/* s6AP */))) ? new T2(0,_12Z/* s6Bj */,_2G/* GHC.Types.False */) : new T2(0,_12Z/* s6Bj */,_8g/* GHC.Types.True */) : (!B(_IO/* GHC.Base.eqString */(_12Z/* s6Bj */.b, _12T/* s6AP */))) ? new T2(0,_12Z/* s6Bj */,_2G/* GHC.Types.False */) : new T2(0,_12Z/* s6Bj */,_8g/* GHC.Types.True */);
          }else{
            var _130/* s6Bs */ = _12Y/* s6Bg */.c,
            _131/* s6Bt */ = E(_12Y/* s6Bg */.a);
            return (_131/* s6Bt */._==0) ? (!B(_IO/* GHC.Base.eqString */(_131/* s6Bt */.a, _12T/* s6AP */))) ? new T3(1,_131/* s6Bt */,_2G/* GHC.Types.False */,_130/* s6Bs */) : new T3(1,_131/* s6Bt */,_8g/* GHC.Types.True */,_130/* s6Bs */) : (!B(_IO/* GHC.Base.eqString */(_131/* s6Bt */.b, _12T/* s6AP */))) ? new T3(1,_131/* s6Bt */,_2G/* GHC.Types.False */,_130/* s6Bs */) : new T3(1,_131/* s6Bt */,_8g/* GHC.Types.True */,_130/* s6Bs */);
          }
        }, _12U/* s6AQ */.b));
      });
      return new T3(5,_12U/* s6AQ */.a,_12W/* s6BB */,_12U/* s6AQ */.c);
    case 6:
      return new T3(6,_12U/* s6AQ */.a,new T(function(){
        if(!B(_IO/* GHC.Base.eqString */(_12T/* s6AP */, _I/* GHC.Types.[] */))){
          return new T1(1,_12T/* s6AP */);
        }else{
          return __Z/* EXTERNAL */;
        }
      }),_12U/* s6AQ */.c);
    default:
      return E(_12U/* s6AQ */);
  }
},
_132/* identity2elementUpdated2 */ = function(_133/* s6BH */, _/* EXTERNAL */){
  var _134/* s6BJ */ = E(_133/* s6BH */);
  switch(_134/* s6BJ */._){
    case 0:
      var _135/* s6BY */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _136/* s6C6 */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_135/* s6BY */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _137/* s6Ca */ = String/* EXTERNAL */(_136/* s6C6 */);
          return fromJSStr/* EXTERNAL */(_137/* s6Ca */);
        })));
      });
    case 1:
      var _138/* s6Cw */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _139/* s6CE */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_138/* s6Cw */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13a/* s6CI */ = String/* EXTERNAL */(_139/* s6CE */);
          return fromJSStr/* EXTERNAL */(_13a/* s6CI */);
        })));
      });
    case 2:
      var _13b/* s6D4 */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13c/* s6Dc */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13b/* s6D4 */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13d/* s6Dg */ = String/* EXTERNAL */(_13c/* s6Dc */);
          return fromJSStr/* EXTERNAL */(_13d/* s6Dg */);
        })));
      });
    case 3:
      var _13e/* s6DC */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13f/* s6DK */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13e/* s6DC */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13g/* s6DO */ = String/* EXTERNAL */(_13f/* s6DK */);
          return fromJSStr/* EXTERNAL */(_13g/* s6DO */);
        })));
      });
    case 4:
      var _13h/* s6DW */ = _134/* s6BJ */.a,
      _13i/* s6DZ */ = _134/* s6BJ */.d,
      _13j/* s6E2 */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_13h/* s6DW */)).b,
      _13k/* s6Eb */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(_13j/* s6E2 */)), _/* EXTERNAL */)),
      _13l/* s6Ej */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13k/* s6Eb */)),
      _13m/* s6Eo */ = B(_Ok/* FormEngine.JQuery.getRadioValue1 */(new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(_13j/* s6E2 */)), _Or/* FormEngine.FormItem.nfiUnitId1 */));
      },1), _/* EXTERNAL */));
      return new T(function(){
        var _13n/* s6Er */ = new T(function(){
          var _13o/* s6Et */ = String/* EXTERNAL */(_13l/* s6Ej */);
          return fromJSStr/* EXTERNAL */(_13o/* s6Et */);
        }),
        _13p/* s6Ez */ = function(_13q/* s6EA */){
          return new T4(4,_13h/* s6DW */,new T(function(){
            var _13r/* s6EC */ = B(_Os/* Text.Read.readEither6 */(B(_Oz/* Text.ParserCombinators.ReadP.run */(_12Q/* FormEngine.FormElement.Updating.updateElementValue1 */, _13n/* s6Er */))));
            if(!_13r/* s6EC */._){
              return __Z/* EXTERNAL */;
            }else{
              if(!E(_13r/* s6EC */.b)._){
                return new T1(1,_13r/* s6EC */.a);
              }else{
                return __Z/* EXTERNAL */;
              }
            }
          }),_2o/* GHC.Base.Nothing */,_13i/* s6DZ */);
        };
        if(!B(_IO/* GHC.Base.eqString */(_13m/* s6Eo */, _Oq/* FormEngine.FormElement.Updating.lvl2 */))){
          var _13s/* s6EK */ = E(_13m/* s6Eo */);
          if(!_13s/* s6EK */._){
            return B(_13p/* s6Ez */(_/* EXTERNAL */));
          }else{
            return new T4(4,_13h/* s6DW */,new T(function(){
              var _13t/* s6EO */ = B(_Os/* Text.Read.readEither6 */(B(_Oz/* Text.ParserCombinators.ReadP.run */(_12Q/* FormEngine.FormElement.Updating.updateElementValue1 */, _13n/* s6Er */))));
              if(!_13t/* s6EO */._){
                return __Z/* EXTERNAL */;
              }else{
                if(!E(_13t/* s6EO */.b)._){
                  return new T1(1,_13t/* s6EO */.a);
                }else{
                  return __Z/* EXTERNAL */;
                }
              }
            }),new T1(1,_13s/* s6EK */),_13i/* s6DZ */);
          }
        }else{
          return B(_13p/* s6Ez */(_/* EXTERNAL */));
        }
      });
    case 5:
      var _13u/* s6Fb */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13v/* s6Fj */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13u/* s6Fb */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13w/* s6Fn */ = String/* EXTERNAL */(_13v/* s6Fj */);
          return fromJSStr/* EXTERNAL */(_13w/* s6Fn */);
        })));
      });
    case 6:
      var _13x/* s6FJ */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13y/* s6FR */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13x/* s6FJ */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13z/* s6FV */ = String/* EXTERNAL */(_13y/* s6FR */);
          return fromJSStr/* EXTERNAL */(_13z/* s6FV */);
        })));
      });
    case 7:
      var _13A/* s6Gh */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13B/* s6Gp */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13A/* s6Gh */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13C/* s6Gt */ = String/* EXTERNAL */(_13B/* s6Gp */);
          return fromJSStr/* EXTERNAL */(_13C/* s6Gt */);
        })));
      });
    case 8:
      var _13D/* s6GQ */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13E/* s6GY */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13D/* s6GQ */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13F/* s6H2 */ = String/* EXTERNAL */(_13E/* s6GY */);
          return fromJSStr/* EXTERNAL */(_13F/* s6H2 */);
        })));
      });
    case 9:
      var _13G/* s6Ho */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13H/* s6Hw */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13G/* s6Ho */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13I/* s6HA */ = String/* EXTERNAL */(_13H/* s6Hw */);
          return fromJSStr/* EXTERNAL */(_13I/* s6HA */);
        })));
      });
    case 10:
      var _13J/* s6HV */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13K/* s6I3 */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13J/* s6HV */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13L/* s6I7 */ = String/* EXTERNAL */(_13K/* s6I3 */);
          return fromJSStr/* EXTERNAL */(_13L/* s6I7 */);
        })));
      });
    default:
      var _13M/* s6Is */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_134/* s6BJ */.a)).b)), _/* EXTERNAL */)),
      _13N/* s6IA */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13M/* s6Is */));
      return new T(function(){
        return B(_12R/* FormEngine.FormElement.Updating.updateElementValue */(_134/* s6BJ */, new T(function(){
          var _13O/* s6IE */ = String/* EXTERNAL */(_13N/* s6IA */);
          return fromJSStr/* EXTERNAL */(_13O/* s6IE */);
        })));
      });
  }
},
_13P/* identity2elementUpdated3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" does not exist"));
}),
_13Q/* identity2elementUpdated4 */ = new T2(1,_LR/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_13R/* $wa */ = function(_13S/* s6Jl */, _13T/* s6Jm */, _/* EXTERNAL */){
  var _13U/* s6Jo */ = B(_O8/* FormEngine.FormElement.Updating.identity2element' */(_13S/* s6Jl */, _13T/* s6Jm */));
  if(!_13U/* s6Jo */._){
    var _13V/* s6Jr */ = new T(function(){
      return B(_12/* GHC.Base.++ */(new T2(1,_LR/* GHC.Show.shows5 */,new T(function(){
        return B(_Nr/* GHC.Show.showLitString */(_13S/* s6Jl */, _13Q/* FormEngine.FormElement.Updating.identity2elementUpdated4 */));
      })), _13P/* FormEngine.FormElement.Updating.identity2elementUpdated3 */));
    }),
    _13W/* s6Jt */ = B(_5K/* FormEngine.JQuery.errorIO1 */(B(unAppCStr/* EXTERNAL */("identity2elementUpdated: element with identity=", _13V/* s6Jr */)), _/* EXTERNAL */));
    return _2o/* GHC.Base.Nothing */;
  }else{
    var _13X/* s6Jx */ = B(_132/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_13U/* s6Jo */.a, _/* EXTERNAL */));
    return new T1(1,_13X/* s6Jx */);
  }
},
_13Y/* setVal2 */ = "(function (val, jq) { jq.val(val).change(); return jq; })",
_13Z/* $wa35 */ = function(_140/* so4M */, _141/* so4N */, _/* EXTERNAL */){
  var _142/* so4X */ = eval/* EXTERNAL */(E(_13Y/* FormEngine.JQuery.setVal2 */));
  return new F(function(){return E(_142/* so4X */)(toJSStr/* EXTERNAL */(E(_140/* so4M */)), _141/* so4N */);});
},
_143/* $fExceptionRecSelError_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RecSelError"));
}),
_144/* $fExceptionRecSelError_wild */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_ON/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_OO/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_143/* Control.Exception.Base.$fExceptionRecSelError_ww4 */),
_145/* $fExceptionRecSelError2 */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_144/* Control.Exception.Base.$fExceptionRecSelError_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_146/* $fExceptionRecSelError1 */ = function(_147/* s4nv0 */){
  return E(_145/* Control.Exception.Base.$fExceptionRecSelError2 */);
},
_148/* $fExceptionRecSelError_$cfromException */ = function(_149/* s4nvr */){
  var _14a/* s4nvs */ = E(_149/* s4nvr */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_14a/* s4nvs */.a)), _146/* Control.Exception.Base.$fExceptionRecSelError1 */, _14a/* s4nvs */.b);});
},
_14b/* $fExceptionRecSelError_$cshow */ = function(_14c/* s4nvj */){
  return E(E(_14c/* s4nvj */).a);
},
_14d/* $fExceptionRecSelError_$ctoException */ = function(_P0/* B1 */){
  return new T2(0,_14e/* Control.Exception.Base.$fExceptionRecSelError */,_P0/* B1 */);
},
_14f/* $fShowRecSelError1 */ = function(_14g/* s4nqO */, _14h/* s4nqP */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_14g/* s4nqO */).a, _14h/* s4nqP */);});
},
_14i/* $fShowRecSelError_$cshowList */ = function(_14j/* s4nvh */, _14k/* s4nvi */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_14f/* Control.Exception.Base.$fShowRecSelError1 */, _14j/* s4nvh */, _14k/* s4nvi */);});
},
_14l/* $fShowRecSelError_$cshowsPrec */ = function(_14m/* s4nvm */, _14n/* s4nvn */, _14o/* s4nvo */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_14n/* s4nvn */).a, _14o/* s4nvo */);});
},
_14p/* $fShowRecSelError */ = new T3(0,_14l/* Control.Exception.Base.$fShowRecSelError_$cshowsPrec */,_14b/* Control.Exception.Base.$fExceptionRecSelError_$cshow */,_14i/* Control.Exception.Base.$fShowRecSelError_$cshowList */),
_14e/* $fExceptionRecSelError */ = new T(function(){
  return new T5(0,_146/* Control.Exception.Base.$fExceptionRecSelError1 */,_14p/* Control.Exception.Base.$fShowRecSelError */,_14d/* Control.Exception.Base.$fExceptionRecSelError_$ctoException */,_148/* Control.Exception.Base.$fExceptionRecSelError_$cfromException */,_14b/* Control.Exception.Base.$fExceptionRecSelError_$cshow */);
}),
_14q/* recSelError */ = function(_14r/* s4nwW */){
  var _14s/* s4nwY */ = new T(function(){
    return B(unAppCStr/* EXTERNAL */("No match in record selector ", new T(function(){
      return B(unCStr/* EXTERNAL */(_14r/* s4nwW */));
    })));
  });
  return new F(function(){return _Ph/* GHC.Exception.throw1 */(new T1(0,_14s/* s4nwY */), _14e/* Control.Exception.Base.$fExceptionRecSelError */);});
},
_14t/* neMaybeValue1 */ = new T(function(){
  return B(_14q/* Control.Exception.Base.recSelError */("neMaybeValue"));
}),
_14u/* $wgo */ = function(_14v/* s6JO */, _14w/* s6JP */){
  while(1){
    var _14x/* s6JQ */ = E(_14v/* s6JO */);
    if(!_14x/* s6JQ */._){
      return E(_14w/* s6JP */);
    }else{
      var _14y/* s6JS */ = _14x/* s6JQ */.b,
      _14z/* s6JT */ = E(_14x/* s6JQ */.a);
      if(_14z/* s6JT */._==4){
        var _14A/* s6JZ */ = E(_14z/* s6JT */.b);
        if(!_14A/* s6JZ */._){
          _14v/* s6JO */ = _14y/* s6JS */;
          continue;
        }else{
          var _14B/*  s6JP */ = _14w/* s6JP */+E(_14A/* s6JZ */.a)|0;
          _14v/* s6JO */ = _14y/* s6JS */;
          _14w/* s6JP */ = _14B/*  s6JP */;
          continue;
        }
      }else{
        return E(_14t/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
      }
    }
  }
},
_14C/* int2Float */ = function(_14D/* sc58 */){
  return E(_14D/* sc58 */);
},
_14E/* numberElem2TB1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_14F/* numberElem2TB2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_14G/* numberElem2TB3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_14H/* numberElem2TB4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_14I/* numberElem2TB */ = function(_14J/* s664 */){
  var _14K/* s665 */ = E(_14J/* s664 */);
  if(_14K/* s665 */._==4){
    var _14L/* s667 */ = _14K/* s665 */.b,
    _14M/* s66a */ = E(_14K/* s665 */.c);
    if(!_14M/* s66a */._){
      return __Z/* EXTERNAL */;
    }else{
      var _14N/* s66b */ = _14M/* s66a */.a;
      if(!B(_IO/* GHC.Base.eqString */(_14N/* s66b */, _14H/* FormEngine.FormElement.FormElement.numberElem2TB4 */))){
        if(!B(_IO/* GHC.Base.eqString */(_14N/* s66b */, _14G/* FormEngine.FormElement.FormElement.numberElem2TB3 */))){
          if(!B(_IO/* GHC.Base.eqString */(_14N/* s66b */, _14F/* FormEngine.FormElement.FormElement.numberElem2TB2 */))){
            if(!B(_IO/* GHC.Base.eqString */(_14N/* s66b */, _14E/* FormEngine.FormElement.FormElement.numberElem2TB1 */))){
              return __Z/* EXTERNAL */;
            }else{
              var _14O/* s66g */ = E(_14L/* s667 */);
              return (_14O/* s66g */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
                return B(_14C/* GHC.Float.RealFracMethods.int2Float */(_14O/* s66g */.a));
              }));
            }
          }else{
            var _14P/* s66j */ = E(_14L/* s667 */);
            return (_14P/* s66j */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
              return E(_14P/* s66j */.a)*1000;
            }));
          }
        }else{
          var _14Q/* s66q */ = E(_14L/* s667 */);
          return (_14Q/* s66q */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
            return E(_14Q/* s66q */.a)*1.0e-6;
          }));
        }
      }else{
        var _14R/* s66x */ = E(_14L/* s667 */);
        return (_14R/* s66x */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
          return E(_14R/* s66x */.a)*1.0e-3;
        }));
      }
    }
  }else{
    return __Z/* EXTERNAL */;
  }
},
_14S/* $wgo1 */ = function(_14T/* s6Ka */, _14U/* s6Kb */){
  while(1){
    var _14V/* s6Kc */ = E(_14T/* s6Ka */);
    if(!_14V/* s6Kc */._){
      return E(_14U/* s6Kb */);
    }else{
      var _14W/* s6Ke */ = _14V/* s6Kc */.b,
      _14X/* s6Kf */ = B(_14I/* FormEngine.FormElement.FormElement.numberElem2TB */(_14V/* s6Kc */.a));
      if(!_14X/* s6Kf */._){
        _14T/* s6Ka */ = _14W/* s6Ke */;
        continue;
      }else{
        var _14Y/*  s6Kb */ = _14U/* s6Kb */+E(_14X/* s6Kf */.a);
        _14T/* s6Ka */ = _14W/* s6Ke */;
        _14U/* s6Kb */ = _14Y/*  s6Kb */;
        continue;
      }
    }
  }
},
_14Z/* disableJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("true"));
}),
_150/* disableJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("readonly"));
}),
_151/* disableJq6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#eee"));
}),
_152/* disableJq7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("background-color"));
}),
_153/* elementId */ = function(_154/* s5Ra */){
  return new F(function(){return _4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_154/* s5Ra */)))).b);});
},
_155/* go */ = function(_156/* s6JI */){
  while(1){
    var _157/* s6JJ */ = E(_156/* s6JI */);
    if(!_157/* s6JJ */._){
      return false;
    }else{
      if(!E(_157/* s6JJ */.a)._){
        return true;
      }else{
        _156/* s6JI */ = _157/* s6JJ */.b;
        continue;
      }
    }
  }
},
_158/* go1 */ = function(_159/* s6K4 */){
  while(1){
    var _15a/* s6K5 */ = E(_159/* s6K4 */);
    if(!_15a/* s6K5 */._){
      return false;
    }else{
      if(!E(_15a/* s6K5 */.a)._){
        return true;
      }else{
        _159/* s6K4 */ = _15a/* s6K5 */.b;
        continue;
      }
    }
  }
},
_15b/* selectIn2 */ = "(function (elId, context) { return $(elId, context); })",
_15c/* $wa18 */ = function(_15d/* so8g */, _15e/* so8h */, _/* EXTERNAL */){
  var _15f/* so8r */ = eval/* EXTERNAL */(E(_15b/* FormEngine.JQuery.selectIn2 */));
  return new F(function(){return E(_15f/* so8r */)(toJSStr/* EXTERNAL */(E(_15d/* so8g */)), _15e/* so8h */);});
},
_15g/* flagPlaceId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_flagPlaceId"));
}),
_15h/* flagPlaceId */ = function(_15i/* stq0 */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_15i/* stq0 */)))).b)), _15g/* FormEngine.FormElement.Identifiers.flagPlaceId1 */);});
},
_15j/* inputFieldUpdate3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".validity-flag"));
}),
_15k/* inputFieldUpdate4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_15l/* invalidImg */ = function(_15m/* s3yB */){
  return E(E(_15m/* s3yB */).c);
},
_15n/* removeJq_f1 */ = new T(function(){
  return (function (jq) { var p = jq.parent(); jq.remove(); return p; });
}),
_15o/* validImg */ = function(_15p/* s3yG */){
  return E(E(_15p/* s3yG */).b);
},
_15q/* inputFieldUpdate2 */ = function(_15r/* s6zV */, _15s/* s6zW */, _15t/* s6zX */, _/* EXTERNAL */){
  var _15u/* s6A1 */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_15k/* FormEngine.FormElement.Updating.inputFieldUpdate4 */, new T(function(){
    return B(_15h/* FormEngine.FormElement.Identifiers.flagPlaceId */(_15r/* s6zV */));
  },1))), _/* EXTERNAL */)),
  _15v/* s6A4 */ = E(_15u/* s6A1 */),
  _15w/* s6A6 */ = B(_15c/* FormEngine.JQuery.$wa18 */(_15j/* FormEngine.FormElement.Updating.inputFieldUpdate3 */, _15v/* s6A4 */, _/* EXTERNAL */)),
  _15x/* s6Ae */ = __app1/* EXTERNAL */(E(_15n/* FormEngine.JQuery.removeJq_f1 */), E(_15w/* s6A6 */));
  if(!E(_15t/* s6zX */)){
    if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_15r/* s6zV */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _15y/* s6Av */ = B(_I6/* FormEngine.JQuery.$wa3 */(B(_15l/* FormEngine.FormContext.invalidImg */(_15s/* s6zW */)), _15v/* s6A4 */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }else{
    if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_15r/* s6zV */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _15z/* s6AL */ = B(_I6/* FormEngine.JQuery.$wa3 */(B(_15o/* FormEngine.FormContext.validImg */(_15s/* s6zW */)), _15v/* s6A4 */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }
},
_15A/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rule application did not unify: "));
}),
_15B/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" @"));
}),
_15C/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid operand in "));
}),
_15D/* selectByIdentity2 */ = "(function (identity) { return $(\'[identity=\"\' + identity + \'\"]\'); })",
_15E/* selectByIdentity1 */ = function(_15F/* snUV */, _/* EXTERNAL */){
  var _15G/* snV5 */ = eval/* EXTERNAL */(E(_15D/* FormEngine.JQuery.selectByIdentity2 */));
  return new F(function(){return E(_15G/* snV5 */)(toJSStr/* EXTERNAL */(E(_15F/* snUV */)));});
},
_15H/* applyRule1 */ = function(_15I/* s6Kk */, _15J/* s6Kl */, _15K/* s6Km */, _/* EXTERNAL */){
  var _15L/* s6Ko */ = function(_/* EXTERNAL */){
    var _15M/* s6Kq */ = E(_15K/* s6Km */);
    switch(_15M/* s6Kq */._){
      case 2:
        var _15N/* s6Ky */ = B(_15E/* FormEngine.JQuery.selectByIdentity1 */(_15M/* s6Kq */.a, _/* EXTERNAL */)),
        _15O/* s6KG */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_15N/* s6Ky */)),
        _15P/* s6KJ */ = B(_15E/* FormEngine.JQuery.selectByIdentity1 */(_15M/* s6Kq */.b, _/* EXTERNAL */)),
        _15Q/* s6KN */ = String/* EXTERNAL */(_15O/* s6KG */),
        _15R/* s6KW */ = B(_13Z/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_15Q/* s6KN */), E(_15P/* s6KJ */), _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 3:
        var _15S/* s6L0 */ = B(_OK/* FormEngine.JQuery.selectByName1 */(B(_153/* FormEngine.FormElement.FormElement.elementId */(_15I/* s6Kk */)), _/* EXTERNAL */)),
        _15T/* s6L3 */ = E(_15S/* s6L0 */),
        _15U/* s6L5 */ = B(_43/* FormEngine.JQuery.$wa2 */(_152/* FormEngine.JQuery.disableJq7 */, _151/* FormEngine.JQuery.disableJq6 */, _15T/* s6L3 */, _/* EXTERNAL */)),
        _15V/* s6L8 */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_150/* FormEngine.JQuery.disableJq3 */, _14Z/* FormEngine.JQuery.disableJq2 */, _15T/* s6L3 */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 4:
        var _15W/* s6Lc */ = B(_132/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_15I/* s6Kk */, _/* EXTERNAL */)),
        _15X/* s6Lf */ = E(_15W/* s6Lc */);
        if(_15X/* s6Lf */._==4){
          var _15Y/* s6Ll */ = E(_15X/* s6Lf */.b);
          if(!_15Y/* s6Ll */._){
            return new F(function(){return _15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_15X/* s6Lf */, _15J/* s6Kl */, _2G/* GHC.Types.False */, _/* EXTERNAL */);});
          }else{
            return new F(function(){return _15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_15X/* s6Lf */, _15J/* s6Kl */, new T(function(){
              return B(A1(_15M/* s6Kq */.a,_15Y/* s6Ll */.a));
            },1), _/* EXTERNAL */);});
          }
        }else{
          return E(_14t/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
        }
        break;
      default:
        var _15Z/* s6Ku */ = new T(function(){
          var _160/* s6Kt */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_15B/* FormEngine.FormElement.Updating.lvl4 */, new T(function(){
              return B(_LH/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_15I/* s6Kk */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(B(_NZ/* FormEngine.FormItem.$fShowFormRule_$cshow */(_15M/* s6Kq */)), _160/* s6Kt */));
        },1);
        return new F(function(){return _5K/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_15A/* FormEngine.FormElement.Updating.lvl3 */, _15Z/* s6Ku */)), _/* EXTERNAL */);});
    }
  };
  if(E(_15I/* s6Kk */)._==4){
    var _161/* s6Lt */ = E(_15K/* s6Km */);
    switch(_161/* s6Lt */._){
      case 0:
        var _162/* s6Lw */ = function(_/* EXTERNAL */, _163/* s6Ly */){
          if(!B(_155/* FormEngine.FormElement.Updating.go */(_163/* s6Ly */))){
            var _164/* s6LA */ = B(_15E/* FormEngine.JQuery.selectByIdentity1 */(_161/* s6Lt */.b, _/* EXTERNAL */)),
            _165/* s6LI */ = B(_13Z/* FormEngine.JQuery.$wa35 */(B(_4e/* GHC.Show.$wshowSignedInt */(0, B(_14u/* FormEngine.FormElement.Updating.$wgo */(B(_5C/* Data.Maybe.catMaybes1 */(_163/* s6Ly */)), 0)), _I/* GHC.Types.[] */)), E(_164/* s6LA */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _166/* s6LN */ = B(_5K/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_15C/* FormEngine.FormElement.Updating.lvl5 */, new T(function(){
              return B(_NZ/* FormEngine.FormItem.$fShowFormRule_$cshow */(_161/* s6Lt */));
            },1))), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        },
        _167/* s6LQ */ = E(_161/* s6Lt */.a);
        if(!_167/* s6LQ */._){
          return new F(function(){return _162/* s6Lw */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _168/* s6LU */ = E(_15J/* s6Kl */).a,
          _169/* s6LX */ = B(_13R/* FormEngine.FormElement.Updating.$wa */(_167/* s6LQ */.a, _168/* s6LU */, _/* EXTERNAL */)),
          _16a/* s6M0 */ = function(_16b/* s6M1 */, _/* EXTERNAL */){
            var _16c/* s6M3 */ = E(_16b/* s6M1 */);
            if(!_16c/* s6M3 */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _16d/* s6M6 */ = B(_13R/* FormEngine.FormElement.Updating.$wa */(_16c/* s6M3 */.a, _168/* s6LU */, _/* EXTERNAL */)),
              _16e/* s6M9 */ = B(_16a/* s6M0 */(_16c/* s6M3 */.b, _/* EXTERNAL */));
              return new T2(1,_16d/* s6M6 */,_16e/* s6M9 */);
            }
          },
          _16f/* s6Md */ = B(_16a/* s6M0 */(_167/* s6LQ */.b, _/* EXTERNAL */));
          return new F(function(){return _162/* s6Lw */(_/* EXTERNAL */, new T2(1,_169/* s6LX */,_16f/* s6Md */));});
        }
        break;
      case 1:
        var _16g/* s6Mj */ = function(_/* EXTERNAL */, _16h/* s6Ml */){
          if(!B(_158/* FormEngine.FormElement.Updating.go1 */(_16h/* s6Ml */))){
            var _16i/* s6Mn */ = B(_15E/* FormEngine.JQuery.selectByIdentity1 */(_161/* s6Lt */.b, _/* EXTERNAL */)),
            _16j/* s6Mt */ = jsShow/* EXTERNAL */(B(_14S/* FormEngine.FormElement.Updating.$wgo1 */(B(_5C/* Data.Maybe.catMaybes1 */(_16h/* s6Ml */)), 0))),
            _16k/* s6MA */ = B(_13Z/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_16j/* s6Mt */), E(_16i/* s6Mn */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            return _0/* GHC.Tuple.() */;
          }
        },
        _16l/* s6MD */ = E(_161/* s6Lt */.a);
        if(!_16l/* s6MD */._){
          return new F(function(){return _16g/* s6Mj */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _16m/* s6MH */ = E(_15J/* s6Kl */).a,
          _16n/* s6MK */ = B(_13R/* FormEngine.FormElement.Updating.$wa */(_16l/* s6MD */.a, _16m/* s6MH */, _/* EXTERNAL */)),
          _16o/* s6MN */ = function(_16p/* s6MO */, _/* EXTERNAL */){
            var _16q/* s6MQ */ = E(_16p/* s6MO */);
            if(!_16q/* s6MQ */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _16r/* s6MT */ = B(_13R/* FormEngine.FormElement.Updating.$wa */(_16q/* s6MQ */.a, _16m/* s6MH */, _/* EXTERNAL */)),
              _16s/* s6MW */ = B(_16o/* s6MN */(_16q/* s6MQ */.b, _/* EXTERNAL */));
              return new T2(1,_16r/* s6MT */,_16s/* s6MW */);
            }
          },
          _16t/* s6N0 */ = B(_16o/* s6MN */(_16l/* s6MD */.b, _/* EXTERNAL */));
          return new F(function(){return _16g/* s6Mj */(_/* EXTERNAL */, new T2(1,_16n/* s6MK */,_16t/* s6N0 */));});
        }
        break;
      default:
        return new F(function(){return _15L/* s6Ko */(_/* EXTERNAL */);});
    }
  }else{
    return new F(function(){return _15L/* s6Ko */(_/* EXTERNAL */);});
  }
},
_16u/* applyRules1 */ = function(_16v/* s6N4 */, _16w/* s6N5 */, _/* EXTERNAL */){
  var _16x/* s6Ni */ = function(_16y/* s6Nj */, _/* EXTERNAL */){
    while(1){
      var _16z/* s6Nl */ = E(_16y/* s6Nj */);
      if(!_16z/* s6Nl */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _16A/* s6No */ = B(_15H/* FormEngine.FormElement.Updating.applyRule1 */(_16v/* s6N4 */, _16w/* s6N5 */, _16z/* s6Nl */.a, _/* EXTERNAL */));
        _16y/* s6Nj */ = _16z/* s6Nl */.b;
        continue;
      }
    }
  };
  return new F(function(){return _16x/* s6Ni */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_16v/* s6N4 */)))).i, _/* EXTERNAL */);});
},
_16B/* isJust */ = function(_16C/* s7rZ */){
  return (E(_16C/* s7rZ */)._==0) ? false : true;
},
_16D/* nfiUnit1 */ = new T(function(){
  return B(_14q/* Control.Exception.Base.recSelError */("nfiUnit"));
}),
_16E/* go */ = function(_16F/* shyP */){
  while(1){
    var _16G/* shyQ */ = E(_16F/* shyP */);
    if(!_16G/* shyQ */._){
      return true;
    }else{
      if(!E(_16G/* shyQ */.a)){
        return false;
      }else{
        _16F/* shyP */ = _16G/* shyQ */.b;
        continue;
      }
    }
  }
},
_16H/* validateElement_go */ = function(_16I/* shyy */){
  while(1){
    var _16J/* shyz */ = E(_16I/* shyy */);
    if(!_16J/* shyz */._){
      return false;
    }else{
      var _16K/* shyB */ = _16J/* shyz */.b,
      _16L/* shyC */ = E(_16J/* shyz */.a);
      if(!_16L/* shyC */._){
        if(!E(_16L/* shyC */.b)){
          _16I/* shyy */ = _16K/* shyB */;
          continue;
        }else{
          return true;
        }
      }else{
        if(!E(_16L/* shyC */.b)){
          _16I/* shyy */ = _16K/* shyB */;
          continue;
        }else{
          return true;
        }
      }
    }
  }
},
_16M/* validateElement_go1 */ = function(_16N/* shyK */){
  while(1){
    var _16O/* shyL */ = E(_16N/* shyK */);
    if(!_16O/* shyL */._){
      return true;
    }else{
      if(!E(_16O/* shyL */.a)){
        return false;
      }else{
        _16N/* shyK */ = _16O/* shyL */.b;
        continue;
      }
    }
  }
},
_16P/* go1 */ = function(_16Q/*  shz1 */){
  while(1){
    var _16R/*  go1 */ = B((function(_16S/* shz1 */){
      var _16T/* shz2 */ = E(_16S/* shz1 */);
      if(!_16T/* shz2 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _16U/* shz4 */ = _16T/* shz2 */.b,
        _16V/* shz5 */ = E(_16T/* shz2 */.a);
        switch(_16V/* shz5 */._){
          case 0:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_16W/* FormEngine.FormElement.Validation.validateElement2 */(_16V/* shz5 */.b));
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 1:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_16V/* shz5 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 2:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_16V/* shz5 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 3:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_16V/* shz5 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 4:
            var _16X/* shAb */ = _16V/* shz5 */.a;
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16X/* shAb */)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                var _16Y/* shAq */ = E(_16V/* shz5 */.b);
                if(!_16Y/* shAq */._){
                  return false;
                }else{
                  if(E(_16Y/* shAq */.a)<0){
                    return false;
                  }else{
                    var _16Z/* shAw */ = E(_16X/* shAb */);
                    if(_16Z/* shAw */._==3){
                      if(E(_16Z/* shAw */.b)._==1){
                        return B(_16B/* Data.Maybe.isJust */(_16V/* shz5 */.c));
                      }else{
                        return true;
                      }
                    }else{
                      return E(_16D/* FormEngine.FormItem.nfiUnit1 */);
                    }
                  }
                }
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 5:
            var _170/* shAE */ = _16V/* shz5 */.a,
            _171/* shAF */ = _16V/* shz5 */.b;
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_170/* shAE */)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_170/* shAE */)).h)){
                  return B(_16M/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_172/* FormEngine.FormElement.Validation.validateElement1 */, _171/* shAF */))));
                }else{
                  if(!B(_16H/* FormEngine.FormElement.Validation.validateElement_go */(_171/* shAF */))){
                    return false;
                  }else{
                    return B(_16M/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_172/* FormEngine.FormElement.Validation.validateElement1 */, _171/* shAF */))));
                  }
                }
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 6:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_16B/* Data.Maybe.isJust */(_16V/* shz5 */.b));
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 7:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_16W/* FormEngine.FormElement.Validation.validateElement2 */(_16V/* shz5 */.b));
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 8:
            return new T2(1,new T(function(){
              if(!E(_16V/* shz5 */.b)){
                return true;
              }else{
                return B(_16W/* FormEngine.FormElement.Validation.validateElement2 */(_16V/* shz5 */.c));
              }
            }),new T(function(){
              return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
            }));
          case 9:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_16W/* FormEngine.FormElement.Validation.validateElement2 */(_16V/* shz5 */.b));
              }),new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          case 10:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8g/* GHC.Types.True */,new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
            break;
          default:
            if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_16V/* shz5 */.a)).h)){
              _16Q/*  shz1 */ = _16U/* shz4 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_8g/* GHC.Types.True */,new T(function(){
                return B(_16P/* FormEngine.FormElement.Validation.go1 */(_16U/* shz4 */));
              }));
            }
        }
      }
    })(_16Q/*  shz1 */));
    if(_16R/*  go1 */!=__continue/* EXTERNAL */){
      return _16R/*  go1 */;
    }
  }
},
_16W/* validateElement2 */ = function(_173/* shCt */){
  return new F(function(){return _16E/* FormEngine.FormElement.Validation.go */(B(_16P/* FormEngine.FormElement.Validation.go1 */(_173/* shCt */)));});
},
_172/* validateElement1 */ = function(_174/* shyU */){
  var _175/* shyV */ = E(_174/* shyU */);
  if(!_175/* shyV */._){
    return true;
  }else{
    return new F(function(){return _16W/* FormEngine.FormElement.Validation.validateElement2 */(_175/* shyV */.c);});
  }
},
_176/* validateElement */ = function(_177/* shCv */){
  var _178/* shCw */ = E(_177/* shCv */);
  switch(_178/* shCw */._){
    case 0:
      return new F(function(){return _16W/* FormEngine.FormElement.Validation.validateElement2 */(_178/* shCw */.b);});
      break;
    case 1:
      return (!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_178/* shCw */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 2:
      return (!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_178/* shCw */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 3:
      return (!B(_Qu/* GHC.Classes.$fEq[]_$s$c==1 */(_178/* shCw */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 4:
      var _179/* shCQ */ = E(_178/* shCw */.b);
      if(!_179/* shCQ */._){
        return false;
      }else{
        if(E(_179/* shCQ */.a)<0){
          return false;
        }else{
          var _17a/* shCW */ = E(_178/* shCw */.a);
          if(_17a/* shCW */._==3){
            if(E(_17a/* shCW */.b)._==1){
              return new F(function(){return _16B/* Data.Maybe.isJust */(_178/* shCw */.c);});
            }else{
              return true;
            }
          }else{
            return E(_16D/* FormEngine.FormItem.nfiUnit1 */);
          }
        }
      }
      break;
    case 5:
      var _17b/* shD3 */ = _178/* shCw */.b;
      if(!E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_178/* shCw */.a)).h)){
        return new F(function(){return _16M/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_172/* FormEngine.FormElement.Validation.validateElement1 */, _17b/* shD3 */)));});
      }else{
        if(!B(_16H/* FormEngine.FormElement.Validation.validateElement_go */(_17b/* shD3 */))){
          return false;
        }else{
          return new F(function(){return _16M/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_172/* FormEngine.FormElement.Validation.validateElement1 */, _17b/* shD3 */)));});
        }
      }
      break;
    case 6:
      return new F(function(){return _16B/* Data.Maybe.isJust */(_178/* shCw */.b);});
      break;
    case 7:
      return new F(function(){return _16W/* FormEngine.FormElement.Validation.validateElement2 */(_178/* shCw */.b);});
      break;
    case 8:
      if(!E(_178/* shCw */.b)){
        return true;
      }else{
        return new F(function(){return _16W/* FormEngine.FormElement.Validation.validateElement2 */(_178/* shCw */.c);});
      }
      break;
    case 9:
      return new F(function(){return _16W/* FormEngine.FormElement.Validation.validateElement2 */(_178/* shCw */.b);});
      break;
    case 10:
      return true;
    default:
      return true;
  }
},
_17c/* $wa */ = function(_17d/* scym */, _17e/* scyn */, _17f/* scyo */, _/* EXTERNAL */){
  var _17g/* scyq */ = B(_132/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_17d/* scym */, _/* EXTERNAL */)),
  _17h/* scyu */ = B(_15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_17g/* scyq */, _17e/* scyn */, new T(function(){
    return B(_176/* FormEngine.FormElement.Validation.validateElement */(_17g/* scyq */));
  },1), _/* EXTERNAL */)),
  _17i/* scyx */ = B(_16u/* FormEngine.FormElement.Updating.applyRules1 */(_17d/* scym */, _17e/* scyn */, _/* EXTERNAL */)),
  _17j/* scyE */ = E(E(_17f/* scyo */).b);
  if(!_17j/* scyE */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_17j/* scyE */.a,_17d/* scym */, _17e/* scyn */, _/* EXTERNAL */);});
  }
},
_17k/* $wa1 */ = function(_17l/* scyG */, _17m/* scyH */, _17n/* scyI */, _/* EXTERNAL */){
  var _17o/* scyK */ = B(_132/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_17l/* scyG */, _/* EXTERNAL */)),
  _17p/* scyO */ = B(_15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_17o/* scyK */, _17m/* scyH */, new T(function(){
    return B(_176/* FormEngine.FormElement.Validation.validateElement */(_17o/* scyK */));
  },1), _/* EXTERNAL */)),
  _17q/* scyR */ = B(_16u/* FormEngine.FormElement.Updating.applyRules1 */(_17l/* scyG */, _17m/* scyH */, _/* EXTERNAL */)),
  _17r/* scyY */ = E(E(_17n/* scyI */).a);
  if(!_17r/* scyY */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_17r/* scyY */.a,_17l/* scyG */, _17m/* scyH */, _/* EXTERNAL */);});
  }
},
_17s/* $wa1 */ = function(_17t/* so1y */, _17u/* so1z */, _/* EXTERNAL */){
  var _17v/* so1E */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_17u/* so1z */),
  _17w/* so1K */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_17v/* so1E */),
  _17x/* so1V */ = eval/* EXTERNAL */(E(_HD/* FormEngine.JQuery.addClass2 */)),
  _17y/* so23 */ = E(_17x/* so1V */)(toJSStr/* EXTERNAL */(E(_17t/* so1y */)), _17w/* so1K */);
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(_17y/* so23 */);});
},
_17z/* $wa23 */ = function(_17A/* snP5 */, _17B/* snP6 */, _/* EXTERNAL */){
  var _17C/* snPb */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_17B/* snP6 */),
  _17D/* snPh */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_17C/* snPb */),
  _17E/* snPl */ = B(_Iu/* FormEngine.JQuery.onClick1 */(_17A/* snP5 */, _17D/* snPh */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_17E/* snPl */));});
},
_17F/* onMouseEnter2 */ = "(function (ev, jq) { jq.mouseenter(ev); })",
_17G/* onMouseEnter1 */ = function(_17H/* snEt */, _17I/* snEu */, _/* EXTERNAL */){
  var _17J/* snEG */ = __createJSFunc/* EXTERNAL */(2, function(_17K/* snEx */, _/* EXTERNAL */){
    var _17L/* snEz */ = B(A2(E(_17H/* snEt */),_17K/* snEx */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _17M/* snEJ */ = E(_17I/* snEu */),
  _17N/* snEO */ = eval/* EXTERNAL */(E(_17F/* FormEngine.JQuery.onMouseEnter2 */)),
  _17O/* snEW */ = E(_17N/* snEO */)(_17J/* snEG */, _17M/* snEJ */);
  return _17M/* snEJ */;
},
_17P/* $wa30 */ = function(_17Q/* snPC */, _17R/* snPD */, _/* EXTERNAL */){
  var _17S/* snPI */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_17R/* snPD */),
  _17T/* snPO */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_17S/* snPI */),
  _17U/* snPS */ = B(_17G/* FormEngine.JQuery.onMouseEnter1 */(_17Q/* snPC */, _17T/* snPO */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_17U/* snPS */));});
},
_17V/* onMouseLeave2 */ = "(function (ev, jq) { jq.mouseleave(ev); })",
_17W/* onMouseLeave1 */ = function(_17X/* snDU */, _17Y/* snDV */, _/* EXTERNAL */){
  var _17Z/* snE7 */ = __createJSFunc/* EXTERNAL */(2, function(_180/* snDY */, _/* EXTERNAL */){
    var _181/* snE0 */ = B(A2(E(_17X/* snDU */),_180/* snDY */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _182/* snEa */ = E(_17Y/* snDV */),
  _183/* snEf */ = eval/* EXTERNAL */(E(_17V/* FormEngine.JQuery.onMouseLeave2 */)),
  _184/* snEn */ = E(_183/* snEf */)(_17Z/* snE7 */, _182/* snEa */);
  return _182/* snEa */;
},
_185/* $wa31 */ = function(_186/* snQ9 */, _187/* snQa */, _/* EXTERNAL */){
  var _188/* snQf */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */)(_187/* snQa */),
  _189/* snQl */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */)(_188/* snQf */),
  _18a/* snQp */ = B(_17W/* FormEngine.JQuery.onMouseLeave1 */(_186/* snQ9 */, _189/* snQl */, _/* EXTERNAL */));
  return new F(function(){return E(_HO/* FormEngine.JQuery.addClassInside_f1 */)(E(_18a/* snQp */));});
},
_18b/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span class=\'short-desc\'>"));
}),
_18c/* setTextInside1 */ = function(_18d/* so7D */, _18e/* so7E */, _/* EXTERNAL */){
  return new F(function(){return _Ib/* FormEngine.JQuery.$wa34 */(_18d/* so7D */, E(_18e/* so7E */), _/* EXTERNAL */);});
},
_18f/* a1 */ = function(_18g/* scxx */, _18h/* scxy */, _/* EXTERNAL */){
  var _18i/* scxL */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_18g/* scxx */)))).e);
  if(!_18i/* scxL */._){
    return _18h/* scxy */;
  }else{
    var _18j/* scxP */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18b/* FormEngine.FormElement.Rendering.lvl */, E(_18h/* scxy */), _/* EXTERNAL */));
    return new F(function(){return _18c/* FormEngine.JQuery.setTextInside1 */(_18i/* scxL */.a, _18j/* scxP */, _/* EXTERNAL */);});
  }
},
_18k/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label>"));
}),
_18l/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label class=\"link\" onclick=\""));
}),
_18m/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\">"));
}),
_18n/* a2 */ = function(_18o/* scxS */, _18p/* scxT */, _/* EXTERNAL */){
  var _18q/* scxW */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_18o/* scxS */)))),
  _18r/* scy6 */ = E(_18q/* scxW */.a);
  if(!_18r/* scy6 */._){
    return _18p/* scxT */;
  }else{
    var _18s/* scy7 */ = _18r/* scy6 */.a,
    _18t/* scy8 */ = E(_18q/* scxW */.g);
    if(!_18t/* scy8 */._){
      var _18u/* scyb */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, E(_18p/* scxT */), _/* EXTERNAL */));
      return new F(function(){return _18c/* FormEngine.JQuery.setTextInside1 */(_18s/* scy7 */, _18u/* scyb */, _/* EXTERNAL */);});
    }else{
      var _18v/* scyj */ = B(_I6/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_18l/* FormEngine.FormElement.Rendering.lvl2 */, new T(function(){
        return B(_12/* GHC.Base.++ */(_18t/* scy8 */.a, _18m/* FormEngine.FormElement.Rendering.lvl3 */));
      },1))), E(_18p/* scxT */), _/* EXTERNAL */));
      return new F(function(){return _18c/* FormEngine.JQuery.setTextInside1 */(_18s/* scy7 */, _18v/* scyj */, _/* EXTERNAL */);});
    }
  }
},
_18w/* a3 */ = function(_18x/* scz0 */, _/* EXTERNAL */){
  var _18y/* scz4 */ = B(_50/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_Lr/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_18x/* scz0 */));
  }))), _/* EXTERNAL */)),
  _18z/* scz9 */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, E(_18y/* scz4 */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_18A/* findSelector2 */ = "(function (elJs, jq) { return jq.find(elJs); })",
_18B/* $wa9 */ = function(_18C/* so7L */, _18D/* so7M */, _/* EXTERNAL */){
  var _18E/* so7W */ = eval/* EXTERNAL */(E(_18A/* FormEngine.JQuery.findSelector2 */));
  return new F(function(){return E(_18E/* so7W */)(toJSStr/* EXTERNAL */(E(_18C/* so7L */)), _18D/* so7M */);});
},
_18F/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("span"));
}),
_18G/* a4 */ = function(_18H/* sczc */, _/* EXTERNAL */){
  var _18I/* sczg */ = B(_50/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_Lr/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_18H/* sczc */));
  }))), _/* EXTERNAL */)),
  _18J/* sczj */ = E(_18I/* sczg */),
  _18K/* sczl */ = B(_18B/* FormEngine.JQuery.$wa9 */(_18F/* FormEngine.FormElement.Rendering.lvl4 */, _18J/* sczj */, _/* EXTERNAL */)),
  _18L/* sczz */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_18H/* sczc */)))).f);
  if(!_18L/* sczz */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _18M/* sczD */ = B(_KQ/* FormEngine.JQuery.$wa26 */(_18L/* sczz */.a, E(_18K/* sczl */), _/* EXTERNAL */)),
    _18N/* sczG */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _IM/* FormEngine.JQuery.appearJq2 */, _18J/* sczj */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_18O/* funcImg */ = function(_18P/* s3Dr */){
  return E(E(_18P/* s3Dr */).a);
},
_18Q/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd\'>"));
}),
_18R/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_18S/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table>"));
}),
_18T/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tbody>"));
}),
_18U/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tr>"));
}),
_18V/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td>"));
}),
_18W/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("more-space"));
}),
_18X/* $wa2 */ = function(_18Y/* sczJ */, _18Z/* sczK */, _190/* sczL */, _191/* sczM */, _192/* sczN */, _/* EXTERNAL */){
  var _193/* sczP */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18S/* FormEngine.FormElement.Rendering.lvl5 */, _192/* sczN */, _/* EXTERNAL */)),
  _194/* sczX */ = B(_17P/* FormEngine.JQuery.$wa30 */(function(_195/* sczU */, _/* EXTERNAL */){
    return new F(function(){return _18G/* FormEngine.FormElement.Rendering.a4 */(_18Z/* sczK */, _/* EXTERNAL */);});
  }, E(_193/* sczP */), _/* EXTERNAL */)),
  _196/* scA5 */ = B(_185/* FormEngine.JQuery.$wa31 */(function(_197/* scA2 */, _/* EXTERNAL */){
    return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a3 */(_18Z/* sczK */, _/* EXTERNAL */);});
  }, E(_194/* sczX */), _/* EXTERNAL */)),
  _198/* scAa */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
  _199/* scAd */ = __app1/* EXTERNAL */(_198/* scAa */, E(_196/* scA5 */)),
  _19a/* scAg */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
  _19b/* scAj */ = __app1/* EXTERNAL */(_19a/* scAg */, _199/* scAd */),
  _19c/* scAm */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18T/* FormEngine.FormElement.Rendering.lvl6 */, _19b/* scAj */, _/* EXTERNAL */)),
  _19d/* scAs */ = __app1/* EXTERNAL */(_198/* scAa */, E(_19c/* scAm */)),
  _19e/* scAw */ = __app1/* EXTERNAL */(_19a/* scAg */, _19d/* scAs */),
  _19f/* scAz */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18U/* FormEngine.FormElement.Rendering.lvl7 */, _19e/* scAw */, _/* EXTERNAL */)),
  _19g/* scAF */ = __app1/* EXTERNAL */(_198/* scAa */, E(_19f/* scAz */)),
  _19h/* scAJ */ = __app1/* EXTERNAL */(_19a/* scAg */, _19g/* scAF */),
  _19i/* scAQ */ = function(_/* EXTERNAL */, _19j/* scAS */){
    var _19k/* scAT */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18Q/* FormEngine.FormElement.Rendering.lvl10 */, _19j/* scAS */, _/* EXTERNAL */)),
    _19l/* scAZ */ = __app1/* EXTERNAL */(_198/* scAa */, E(_19k/* scAT */)),
    _19m/* scB3 */ = __app1/* EXTERNAL */(_19a/* scAg */, _19l/* scAZ */),
    _19n/* scB6 */ = B(_HE/* FormEngine.JQuery.$wa */(_18W/* FormEngine.FormElement.Rendering.lvl9 */, _19m/* scB3 */, _/* EXTERNAL */)),
    _19o/* scB9 */ = B(_18n/* FormEngine.FormElement.Rendering.a2 */(_18Z/* sczK */, _19n/* scB6 */, _/* EXTERNAL */)),
    _19p/* scBe */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
    _19q/* scBh */ = __app1/* EXTERNAL */(_19p/* scBe */, E(_19o/* scB9 */)),
    _19r/* scBk */ = B(A1(_18Y/* sczJ */,_/* EXTERNAL */)),
    _19s/* scBn */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18V/* FormEngine.FormElement.Rendering.lvl8 */, _19q/* scBh */, _/* EXTERNAL */)),
    _19t/* scBt */ = __app1/* EXTERNAL */(_198/* scAa */, E(_19s/* scBn */)),
    _19u/* scBx */ = __app1/* EXTERNAL */(_19a/* scAg */, _19t/* scBt */),
    _19v/* scBF */ = __app2/* EXTERNAL */(E(_Ii/* FormEngine.JQuery.appendJq_f1 */), E(_19r/* scBk */), _19u/* scBx */),
    _19w/* scBJ */ = __app1/* EXTERNAL */(_19p/* scBe */, _19v/* scBF */),
    _19x/* scBM */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18V/* FormEngine.FormElement.Rendering.lvl8 */, _19w/* scBJ */, _/* EXTERNAL */)),
    _19y/* scBS */ = B(_HR/* FormEngine.JQuery.$wa20 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
      return B(_15h/* FormEngine.FormElement.Identifiers.flagPlaceId */(_18Z/* sczK */));
    },1), E(_19x/* scBM */), _/* EXTERNAL */)),
    _19z/* scBY */ = __app1/* EXTERNAL */(_19p/* scBe */, E(_19y/* scBS */)),
    _19A/* scC2 */ = __app1/* EXTERNAL */(_19p/* scBe */, _19z/* scBY */),
    _19B/* scC6 */ = __app1/* EXTERNAL */(_19p/* scBe */, _19A/* scC2 */);
    return new F(function(){return _18f/* FormEngine.FormElement.Rendering.a1 */(_18Z/* sczK */, _19B/* scC6 */, _/* EXTERNAL */);});
  },
  _19C/* scCa */ = E(E(_191/* sczM */).c);
  if(!_19C/* scCa */._){
    return new F(function(){return _19i/* scAQ */(_/* EXTERNAL */, _19h/* scAJ */);});
  }else{
    var _19D/* scCb */ = _19C/* scCa */.a,
    _19E/* scCc */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18V/* FormEngine.FormElement.Rendering.lvl8 */, _19h/* scAJ */, _/* EXTERNAL */)),
    _19F/* scCi */ = __app1/* EXTERNAL */(_198/* scAa */, E(_19E/* scCc */)),
    _19G/* scCm */ = __app1/* EXTERNAL */(_19a/* scAg */, _19F/* scCi */),
    _19H/* scCp */ = B(_HE/* FormEngine.JQuery.$wa */(_18W/* FormEngine.FormElement.Rendering.lvl9 */, _19G/* scCm */, _/* EXTERNAL */)),
    _19I/* scCv */ = B(_I6/* FormEngine.JQuery.$wa3 */(B(_18O/* FormEngine.Functionality.funcImg */(_19D/* scCb */)), E(_19H/* scCp */), _/* EXTERNAL */)),
    _19J/* scCA */ = new T(function(){
      return B(A2(E(_19D/* scCb */).b,_18Z/* sczK */, _190/* sczL */));
    }),
    _19K/* scCG */ = B(_17z/* FormEngine.JQuery.$wa23 */(function(_19L/* scCE */){
      return E(_19J/* scCA */);
    }, E(_19I/* scCv */), _/* EXTERNAL */)),
    _19M/* scCO */ = __app1/* EXTERNAL */(E(_HO/* FormEngine.JQuery.addClassInside_f1 */), E(_19K/* scCG */));
    return new F(function(){return _19i/* scAQ */(_/* EXTERNAL */, _19M/* scCO */);});
  }
},
_19N/* a5 */ = function(_19O/* scCW */, _/* EXTERNAL */){
  while(1){
    var _19P/* scCY */ = E(_19O/* scCW */);
    if(!_19P/* scCY */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _19Q/* scD3 */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, E(_19P/* scCY */.a), _/* EXTERNAL */));
      _19O/* scCW */ = _19P/* scCY */.b;
      continue;
    }
  }
},
_19R/* appendT1 */ = function(_19S/* so0t */, _19T/* so0u */, _/* EXTERNAL */){
  return new F(function(){return _I6/* FormEngine.JQuery.$wa3 */(_19S/* so0t */, E(_19T/* so0u */), _/* EXTERNAL */);});
},
_19U/* checkboxId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_optional_group"));
}),
_19V/* checkboxId */ = function(_19W/* stoS */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_19W/* stoS */)))).b)), _19U/* FormEngine.FormElement.Identifiers.checkboxId1 */);});
},
_19X/* errorjq1 */ = function(_19Y/* snJM */, _19Z/* snJN */, _/* EXTERNAL */){
  var _1a0/* snJX */ = eval/* EXTERNAL */(E(_5J/* FormEngine.JQuery.errorIO2 */)),
  _1a1/* snK5 */ = E(_1a0/* snJX */)(toJSStr/* EXTERNAL */(E(_19Y/* snJM */)));
  return _19Z/* snJN */;
},
_1a2/* go */ = function(_1a3/* scCR */, _1a4/* scCS */){
  while(1){
    var _1a5/* scCT */ = E(_1a3/* scCR */);
    if(!_1a5/* scCT */._){
      return E(_1a4/* scCS */);
    }else{
      _1a3/* scCR */ = _1a5/* scCT */.b;
      _1a4/* scCS */ = _1a5/* scCT */.a;
      continue;
    }
  }
},
_1a6/* isChecked_f1 */ = new T(function(){
  return (function (jq) { return jq.prop('checked') === true; });
}),
_1a7/* isRadioSelected_f1 */ = new T(function(){
  return (function (jq) { return jq.length; });
}),
_1a8/* isRadioSelected1 */ = function(_1a9/* snWy */, _/* EXTERNAL */){
  var _1aa/* snWJ */ = eval/* EXTERNAL */(E(_Oh/* FormEngine.JQuery.getRadioValue2 */)),
  _1ab/* snWR */ = E(_1aa/* snWJ */)(toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Oj/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1a9/* snWy */, _Oi/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _1ac/* snWX */ = E(_1a7/* FormEngine.JQuery.isRadioSelected_f1 */)(_1ab/* snWR */);
  return new T(function(){
    var _1ad/* snX1 */ = Number/* EXTERNAL */(_1ac/* snWX */),
    _1ae/* snX5 */ = jsTrunc/* EXTERNAL */(_1ad/* snX1 */);
    return _1ae/* snX5 */>0;
  });
},
_1af/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_1ag/* errorEmptyList */ = function(_1ah/* s9sr */){
  return new F(function(){return err/* EXTERNAL */(B(_12/* GHC.Base.++ */(_6K/* GHC.List.prel_list_str */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1ah/* s9sr */, _1af/* GHC.List.lvl */));
  },1))));});
},
_1ai/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_1aj/* last1 */ = new T(function(){
  return B(_1ag/* GHC.List.errorEmptyList */(_1ai/* GHC.List.lvl16 */));
}),
_1ak/* lfiAvailableOptions1 */ = new T(function(){
  return B(_14q/* Control.Exception.Base.recSelError */("lfiAvailableOptions"));
}),
_1al/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Submit"));
}),
_1am/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("value"));
}),
_1an/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'button\' class=\'submit\'>"));
}),
_1ao/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd more-space\' style=\'text-align: center\'>"));
}),
_1ap/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table style=\'margin-top: 10px\'>"));
}),
_1aq/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save"));
}),
_1ar/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'submit\'>"));
}),
_1as/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElement rendering not implemented yet"));
}),
_1at/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-section\'>"));
}),
_1au/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u25be"));
}),
_1av/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1aw/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("checked"));
}),
_1ax/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("name"));
}),
_1ay/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'checkbox\'>"));
}),
_1az/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("level"));
}),
_1aA/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-group\'>"));
}),
_1aB/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(">"));
}),
_1aC/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h"));
}),
_1aD/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("framed"));
}),
_1aE/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'simple-group\'>"));
}),
_1aF/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("selected"));
}),
_1aG/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<option>"));
}),
_1aH/* lvl34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("identity"));
}),
_1aI/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<select>"));
}),
_1aJ/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div>"));
}),
_1aK/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<br>"));
}),
_1aL/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'radio\'>"));
}),
_1aM/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div></div>"));
}),
_1aN/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;&nbsp;"));
}),
_1aO/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;"));
}),
_1aP/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'number\'>"));
}),
_1aQ/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'email\'>"));
}),
_1aR/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<textarea>"));
}),
_1aS/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'text\'>"));
}),
_1aT/* lvl46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("renderElement did not unify"));
}),
_1aU/* lvl47 */ = new T(function(){
  return B(_4e/* GHC.Show.$wshowSignedInt */(0, 0, _I/* GHC.Types.[] */));
}),
_1aV/* onBlur2 */ = "(function (ev, jq) { jq.blur(ev); })",
_1aW/* onBlur1 */ = function(_1aX/* snGJ */, _1aY/* snGK */, _/* EXTERNAL */){
  var _1aZ/* snGW */ = __createJSFunc/* EXTERNAL */(2, function(_1b0/* snGN */, _/* EXTERNAL */){
    var _1b1/* snGP */ = B(A2(E(_1aX/* snGJ */),_1b0/* snGN */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1b2/* snGZ */ = E(_1aY/* snGK */),
  _1b3/* snH4 */ = eval/* EXTERNAL */(E(_1aV/* FormEngine.JQuery.onBlur2 */)),
  _1b4/* snHc */ = E(_1b3/* snH4 */)(_1aZ/* snGW */, _1b2/* snGZ */);
  return _1b2/* snGZ */;
},
_1b5/* onChange2 */ = "(function (ev, jq) { jq.change(ev); })",
_1b6/* onChange1 */ = function(_1b7/* snF2 */, _1b8/* snF3 */, _/* EXTERNAL */){
  var _1b9/* snFf */ = __createJSFunc/* EXTERNAL */(2, function(_1ba/* snF6 */, _/* EXTERNAL */){
    var _1bb/* snF8 */ = B(A2(E(_1b7/* snF2 */),_1ba/* snF6 */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1bc/* snFi */ = E(_1b8/* snF3 */),
  _1bd/* snFn */ = eval/* EXTERNAL */(E(_1b5/* FormEngine.JQuery.onChange2 */)),
  _1be/* snFv */ = E(_1bd/* snFn */)(_1b9/* snFf */, _1bc/* snFi */);
  return _1bc/* snFi */;
},
_1bf/* onKeyup2 */ = "(function (ev, jq) { jq.keyup(ev); })",
_1bg/* onKeyup1 */ = function(_1bh/* snGa */, _1bi/* snGb */, _/* EXTERNAL */){
  var _1bj/* snGn */ = __createJSFunc/* EXTERNAL */(2, function(_1bk/* snGe */, _/* EXTERNAL */){
    var _1bl/* snGg */ = B(A2(E(_1bh/* snGa */),_1bk/* snGe */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1bm/* snGq */ = E(_1bi/* snGb */),
  _1bn/* snGv */ = eval/* EXTERNAL */(E(_1bf/* FormEngine.JQuery.onKeyup2 */)),
  _1bo/* snGD */ = E(_1bn/* snGv */)(_1bj/* snGn */, _1bm/* snGq */);
  return _1bm/* snGq */;
},
_1bp/* optionElemValue */ = function(_1bq/* s5XH */){
  var _1br/* s5XI */ = E(_1bq/* s5XH */);
  if(!_1br/* s5XI */._){
    var _1bs/* s5XL */ = E(_1br/* s5XI */.a);
    return (_1bs/* s5XL */._==0) ? E(_1bs/* s5XL */.a) : E(_1bs/* s5XL */.b);
  }else{
    var _1bt/* s5XT */ = E(_1br/* s5XI */.a);
    return (_1bt/* s5XT */._==0) ? E(_1bt/* s5XT */.a) : E(_1bt/* s5XT */.b);
  }
},
_1bu/* optionSectionId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_detail"));
}),
_1bv/* filter */ = function(_1bw/*  s9DD */, _1bx/*  s9DE */){
  while(1){
    var _1by/*  filter */ = B((function(_1bz/* s9DD */, _1bA/* s9DE */){
      var _1bB/* s9DF */ = E(_1bA/* s9DE */);
      if(!_1bB/* s9DF */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1bC/* s9DG */ = _1bB/* s9DF */.a,
        _1bD/* s9DH */ = _1bB/* s9DF */.b;
        if(!B(A1(_1bz/* s9DD */,_1bC/* s9DG */))){
          var _1bE/*   s9DD */ = _1bz/* s9DD */;
          _1bw/*  s9DD */ = _1bE/*   s9DD */;
          _1bx/*  s9DE */ = _1bD/* s9DH */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1bC/* s9DG */,new T(function(){
            return B(_1bv/* GHC.List.filter */(_1bz/* s9DD */, _1bD/* s9DH */));
          }));
        }
      }
    })(_1bw/*  s9DD */, _1bx/*  s9DE */));
    if(_1by/*  filter */!=__continue/* EXTERNAL */){
      return _1by/*  filter */;
    }
  }
},
_1bF/* $wlvl */ = function(_1bG/* stp5 */){
  var _1bH/* stp6 */ = function(_1bI/* stp7 */){
    var _1bJ/* stp8 */ = function(_1bK/* stp9 */){
      if(_1bG/* stp5 */<48){
        switch(E(_1bG/* stp5 */)){
          case 45:
            return true;
          case 95:
            return true;
          default:
            return false;
        }
      }else{
        if(_1bG/* stp5 */>57){
          switch(E(_1bG/* stp5 */)){
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
    if(_1bG/* stp5 */<97){
      return new F(function(){return _1bJ/* stp8 */(_/* EXTERNAL */);});
    }else{
      if(_1bG/* stp5 */>122){
        return new F(function(){return _1bJ/* stp8 */(_/* EXTERNAL */);});
      }else{
        return true;
      }
    }
  };
  if(_1bG/* stp5 */<65){
    return new F(function(){return _1bH/* stp6 */(_/* EXTERNAL */);});
  }else{
    if(_1bG/* stp5 */>90){
      return new F(function(){return _1bH/* stp6 */(_/* EXTERNAL */);});
    }else{
      return true;
    }
  }
},
_1bL/* radioId1 */ = function(_1bM/* stpo */){
  return new F(function(){return _1bF/* FormEngine.FormElement.Identifiers.$wlvl */(E(_1bM/* stpo */));});
},
_1bN/* radioId2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_1bO/* radioId */ = function(_1bP/* stpr */, _1bQ/* stps */){
  var _1bR/* stpW */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_1bN/* FormEngine.FormElement.Identifiers.radioId2 */, new T(function(){
      var _1bS/* stpF */ = E(_1bQ/* stps */);
      if(!_1bS/* stpF */._){
        var _1bT/* stpI */ = E(_1bS/* stpF */.a);
        if(!_1bT/* stpI */._){
          return B(_1bv/* GHC.List.filter */(_1bL/* FormEngine.FormElement.Identifiers.radioId1 */, _1bT/* stpI */.a));
        }else{
          return B(_1bv/* GHC.List.filter */(_1bL/* FormEngine.FormElement.Identifiers.radioId1 */, _1bT/* stpI */.b));
        }
      }else{
        var _1bU/* stpQ */ = E(_1bS/* stpF */.a);
        if(!_1bU/* stpQ */._){
          return B(_1bv/* GHC.List.filter */(_1bL/* FormEngine.FormElement.Identifiers.radioId1 */, _1bU/* stpQ */.a));
        }else{
          return B(_1bv/* GHC.List.filter */(_1bL/* FormEngine.FormElement.Identifiers.radioId1 */, _1bU/* stpQ */.b));
        }
      }
    },1)));
  },1);
  return new F(function(){return _12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_1bP/* stpr */)))).b)), _1bR/* stpW */);});
},
_1bV/* target_f1 */ = new T(function(){
  return (function (js) {return $(js.target); });
}),
_1bW/* foldElements2 */ = function(_1bX/* scD6 */, _1bY/* scD7 */, _1bZ/* scD8 */, _1c0/* scD9 */, _/* EXTERNAL */){
  var _1c1/* scDb */ = function(_1c2/* scDc */, _/* EXTERNAL */){
    return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1bX/* scD6 */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
  },
  _1c3/* scDe */ = E(_1bX/* scD6 */);
  switch(_1c3/* scDe */._){
    case 0:
      return new F(function(){return _19X/* FormEngine.JQuery.errorjq1 */(_1aT/* FormEngine.FormElement.Rendering.lvl46 */, _1c0/* scD9 */, _/* EXTERNAL */);});
      break;
    case 1:
      var _1c4/* scEo */ = function(_/* EXTERNAL */){
        var _1c5/* scDo */ = B(_50/* FormEngine.JQuery.select1 */(_1aS/* FormEngine.FormElement.Rendering.lvl45 */, _/* EXTERNAL */)),
        _1c6/* scDr */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1c3/* scDe */.a)),
        _1c7/* scDE */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1c6/* scDr */.b)), E(_1c5/* scDo */), _/* EXTERNAL */)),
        _1c8/* scDH */ = function(_/* EXTERNAL */, _1c9/* scDJ */){
          var _1ca/* scDK */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1c3/* scDe */.b, _1c9/* scDJ */, _/* EXTERNAL */)),
          _1cb/* scDQ */ = B(_17G/* FormEngine.JQuery.onMouseEnter1 */(function(_1cc/* scDN */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1ca/* scDK */, _/* EXTERNAL */)),
          _1cd/* scDW */ = B(_1bg/* FormEngine.JQuery.onKeyup1 */(function(_1ce/* scDT */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cb/* scDQ */, _/* EXTERNAL */)),
          _1cf/* scE2 */ = B(_1aW/* FormEngine.JQuery.onBlur1 */(function(_1cg/* scDZ */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cd/* scDW */, _/* EXTERNAL */));
          return new F(function(){return _17W/* FormEngine.JQuery.onMouseLeave1 */(function(_1ch/* scE5 */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cf/* scE2 */, _/* EXTERNAL */);});
        },
        _1ci/* scE8 */ = E(_1c6/* scDr */.c);
        if(!_1ci/* scE8 */._){
          var _1cj/* scEb */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1c7/* scDE */), _/* EXTERNAL */));
          return new F(function(){return _1c8/* scDH */(_/* EXTERNAL */, E(_1cj/* scEb */));});
        }else{
          var _1ck/* scEj */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1ci/* scE8 */.a, E(_1c7/* scDE */), _/* EXTERNAL */));
          return new F(function(){return _1c8/* scDH */(_/* EXTERNAL */, E(_1ck/* scEj */));});
        }
      };
      return new F(function(){return _18X/* FormEngine.FormElement.Rendering.$wa2 */(_1c4/* scEo */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */);});
      break;
    case 2:
      var _1cl/* scFv */ = function(_/* EXTERNAL */){
        var _1cm/* scEv */ = B(_50/* FormEngine.JQuery.select1 */(_1aR/* FormEngine.FormElement.Rendering.lvl44 */, _/* EXTERNAL */)),
        _1cn/* scEy */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1c3/* scDe */.a)),
        _1co/* scEL */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1cn/* scEy */.b)), E(_1cm/* scEv */), _/* EXTERNAL */)),
        _1cp/* scEO */ = function(_/* EXTERNAL */, _1cq/* scEQ */){
          var _1cr/* scER */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1c3/* scDe */.b, _1cq/* scEQ */, _/* EXTERNAL */)),
          _1cs/* scEX */ = B(_17G/* FormEngine.JQuery.onMouseEnter1 */(function(_1ct/* scEU */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cr/* scER */, _/* EXTERNAL */)),
          _1cu/* scF3 */ = B(_1bg/* FormEngine.JQuery.onKeyup1 */(function(_1cv/* scF0 */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cs/* scEX */, _/* EXTERNAL */)),
          _1cw/* scF9 */ = B(_1aW/* FormEngine.JQuery.onBlur1 */(function(_1cx/* scF6 */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cu/* scF3 */, _/* EXTERNAL */));
          return new F(function(){return _17W/* FormEngine.JQuery.onMouseLeave1 */(function(_1cy/* scFc */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cw/* scF9 */, _/* EXTERNAL */);});
        },
        _1cz/* scFf */ = E(_1cn/* scEy */.c);
        if(!_1cz/* scFf */._){
          var _1cA/* scFi */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1co/* scEL */), _/* EXTERNAL */));
          return new F(function(){return _1cp/* scEO */(_/* EXTERNAL */, E(_1cA/* scFi */));});
        }else{
          var _1cB/* scFq */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1cz/* scFf */.a, E(_1co/* scEL */), _/* EXTERNAL */));
          return new F(function(){return _1cp/* scEO */(_/* EXTERNAL */, E(_1cB/* scFq */));});
        }
      };
      return new F(function(){return _18X/* FormEngine.FormElement.Rendering.$wa2 */(_1cl/* scFv */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */);});
      break;
    case 3:
      var _1cC/* scGC */ = function(_/* EXTERNAL */){
        var _1cD/* scFC */ = B(_50/* FormEngine.JQuery.select1 */(_1aQ/* FormEngine.FormElement.Rendering.lvl43 */, _/* EXTERNAL */)),
        _1cE/* scFF */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1c3/* scDe */.a)),
        _1cF/* scFS */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1cE/* scFF */.b)), E(_1cD/* scFC */), _/* EXTERNAL */)),
        _1cG/* scFV */ = function(_/* EXTERNAL */, _1cH/* scFX */){
          var _1cI/* scFY */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1c3/* scDe */.b, _1cH/* scFX */, _/* EXTERNAL */)),
          _1cJ/* scG4 */ = B(_17G/* FormEngine.JQuery.onMouseEnter1 */(function(_1cK/* scG1 */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cI/* scFY */, _/* EXTERNAL */)),
          _1cL/* scGa */ = B(_1bg/* FormEngine.JQuery.onKeyup1 */(function(_1cM/* scG7 */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cJ/* scG4 */, _/* EXTERNAL */)),
          _1cN/* scGg */ = B(_1aW/* FormEngine.JQuery.onBlur1 */(function(_1cO/* scGd */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cL/* scGa */, _/* EXTERNAL */));
          return new F(function(){return _17W/* FormEngine.JQuery.onMouseLeave1 */(function(_1cP/* scGj */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1cN/* scGg */, _/* EXTERNAL */);});
        },
        _1cQ/* scGm */ = E(_1cE/* scFF */.c);
        if(!_1cQ/* scGm */._){
          var _1cR/* scGp */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1cF/* scFS */), _/* EXTERNAL */));
          return new F(function(){return _1cG/* scFV */(_/* EXTERNAL */, E(_1cR/* scGp */));});
        }else{
          var _1cS/* scGx */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1cQ/* scGm */.a, E(_1cF/* scFS */), _/* EXTERNAL */));
          return new F(function(){return _1cG/* scFV */(_/* EXTERNAL */, E(_1cS/* scGx */));});
        }
      };
      return new F(function(){return _18X/* FormEngine.FormElement.Rendering.$wa2 */(_1cC/* scGC */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */);});
      break;
    case 4:
      var _1cT/* scGD */ = _1c3/* scDe */.a,
      _1cU/* scGJ */ = function(_1cV/* scGK */, _/* EXTERNAL */){
        return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
      },
      _1cW/* scMs */ = function(_/* EXTERNAL */){
        var _1cX/* scGN */ = B(_50/* FormEngine.JQuery.select1 */(_1aP/* FormEngine.FormElement.Rendering.lvl42 */, _/* EXTERNAL */)),
        _1cY/* scGQ */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1cT/* scGD */)),
        _1cZ/* scGS */ = _1cY/* scGQ */.b,
        _1d0/* scH3 */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1cZ/* scGS */)), E(_1cX/* scGN */), _/* EXTERNAL */)),
        _1d1/* scH9 */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1cZ/* scGS */)), E(_1d0/* scH3 */), _/* EXTERNAL */)),
        _1d2/* scHc */ = function(_/* EXTERNAL */, _1d3/* scHe */){
          var _1d4/* scHf */ = function(_/* EXTERNAL */, _1d5/* scHh */){
            var _1d6/* scHl */ = B(_17G/* FormEngine.JQuery.onMouseEnter1 */(function(_1d7/* scHi */, _/* EXTERNAL */){
              return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
            }, _1d5/* scHh */, _/* EXTERNAL */)),
            _1d8/* scHr */ = B(_1bg/* FormEngine.JQuery.onKeyup1 */(function(_1d9/* scHo */, _/* EXTERNAL */){
              return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
            }, _1d6/* scHl */, _/* EXTERNAL */)),
            _1da/* scHx */ = B(_1aW/* FormEngine.JQuery.onBlur1 */(function(_1db/* scHu */, _/* EXTERNAL */){
              return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
            }, _1d8/* scHr */, _/* EXTERNAL */)),
            _1dc/* scHD */ = B(_17W/* FormEngine.JQuery.onMouseLeave1 */(function(_1dd/* scHA */, _/* EXTERNAL */){
              return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
            }, _1da/* scHx */, _/* EXTERNAL */)),
            _1de/* scHI */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aO/* FormEngine.FormElement.Rendering.lvl41 */, E(_1dc/* scHD */), _/* EXTERNAL */)),
            _1df/* scHL */ = E(_1cT/* scGD */);
            if(_1df/* scHL */._==3){
              var _1dg/* scHP */ = E(_1df/* scHL */.b);
              switch(_1dg/* scHP */._){
                case 0:
                  return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1dg/* scHP */.a, _1de/* scHI */, _/* EXTERNAL */);});
                  break;
                case 1:
                  var _1dh/* scHS */ = new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(E(_1df/* scHL */.a).b)), _Or/* FormEngine.FormItem.nfiUnitId1 */));
                  }),
                  _1di/* scI4 */ = E(_1dg/* scHP */.a);
                  if(!_1di/* scI4 */._){
                    return _1de/* scHI */;
                  }else{
                    var _1dj/* scI5 */ = _1di/* scI4 */.a,
                    _1dk/* scI6 */ = _1di/* scI4 */.b,
                    _1dl/* scI9 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl38 */, E(_1de/* scHI */), _/* EXTERNAL */)),
                    _1dm/* scIe */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1dj/* scI5 */, E(_1dl/* scI9 */), _/* EXTERNAL */)),
                    _1dn/* scIj */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, _1dh/* scHS */, E(_1dm/* scIe */), _/* EXTERNAL */)),
                    _1do/* scIo */ = B(_17P/* FormEngine.JQuery.$wa30 */(_1c1/* scDb */, E(_1dn/* scIj */), _/* EXTERNAL */)),
                    _1dp/* scIt */ = B(_17z/* FormEngine.JQuery.$wa23 */(_1c1/* scDb */, E(_1do/* scIo */), _/* EXTERNAL */)),
                    _1dq/* scIy */ = B(_185/* FormEngine.JQuery.$wa31 */(_1cU/* scGJ */, E(_1dp/* scIt */), _/* EXTERNAL */)),
                    _1dr/* scIB */ = function(_/* EXTERNAL */, _1ds/* scID */){
                      var _1dt/* scIE */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, _1ds/* scID */, _/* EXTERNAL */)),
                      _1du/* scIJ */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1dj/* scI5 */, E(_1dt/* scIE */), _/* EXTERNAL */));
                      return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aN/* FormEngine.FormElement.Rendering.lvl40 */, _1du/* scIJ */, _/* EXTERNAL */);});
                    },
                    _1dv/* scIM */ = E(_1c3/* scDe */.c);
                    if(!_1dv/* scIM */._){
                      var _1dw/* scIP */ = B(_1dr/* scIB */(_/* EXTERNAL */, E(_1dq/* scIy */))),
                      _1dx/* scIS */ = function(_1dy/* scIT */, _1dz/* scIU */, _/* EXTERNAL */){
                        while(1){
                          var _1dA/* scIW */ = E(_1dy/* scIT */);
                          if(!_1dA/* scIW */._){
                            return _1dz/* scIU */;
                          }else{
                            var _1dB/* scIX */ = _1dA/* scIW */.a,
                            _1dC/* scJ1 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl38 */, E(_1dz/* scIU */), _/* EXTERNAL */)),
                            _1dD/* scJ6 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1dB/* scIX */, E(_1dC/* scJ1 */), _/* EXTERNAL */)),
                            _1dE/* scJb */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, _1dh/* scHS */, E(_1dD/* scJ6 */), _/* EXTERNAL */)),
                            _1dF/* scJg */ = B(_17P/* FormEngine.JQuery.$wa30 */(_1c1/* scDb */, E(_1dE/* scJb */), _/* EXTERNAL */)),
                            _1dG/* scJl */ = B(_17z/* FormEngine.JQuery.$wa23 */(_1c1/* scDb */, E(_1dF/* scJg */), _/* EXTERNAL */)),
                            _1dH/* scJq */ = B(_185/* FormEngine.JQuery.$wa31 */(_1cU/* scGJ */, E(_1dG/* scJl */), _/* EXTERNAL */)),
                            _1dI/* scJv */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, E(_1dH/* scJq */), _/* EXTERNAL */)),
                            _1dJ/* scJA */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1dB/* scIX */, E(_1dI/* scJv */), _/* EXTERNAL */)),
                            _1dK/* scJF */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aN/* FormEngine.FormElement.Rendering.lvl40 */, E(_1dJ/* scJA */), _/* EXTERNAL */));
                            _1dy/* scIT */ = _1dA/* scIW */.b;
                            _1dz/* scIU */ = _1dK/* scJF */;
                            continue;
                          }
                        }
                      };
                      return new F(function(){return _1dx/* scIS */(_1dk/* scI6 */, _1dw/* scIP */, _/* EXTERNAL */);});
                    }else{
                      var _1dL/* scJI */ = _1dv/* scIM */.a;
                      if(!B(_IO/* GHC.Base.eqString */(_1dL/* scJI */, _1dj/* scI5 */))){
                        var _1dM/* scJM */ = B(_1dr/* scIB */(_/* EXTERNAL */, E(_1dq/* scIy */))),
                        _1dN/* scJP */ = function(_1dO/*  scJQ */, _1dP/*  scJR */, _/* EXTERNAL */){
                          while(1){
                            var _1dQ/*  scJP */ = B((function(_1dR/* scJQ */, _1dS/* scJR */, _/* EXTERNAL */){
                              var _1dT/* scJT */ = E(_1dR/* scJQ */);
                              if(!_1dT/* scJT */._){
                                return _1dS/* scJR */;
                              }else{
                                var _1dU/* scJU */ = _1dT/* scJT */.a,
                                _1dV/* scJV */ = _1dT/* scJT */.b,
                                _1dW/* scJY */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl38 */, E(_1dS/* scJR */), _/* EXTERNAL */)),
                                _1dX/* scK3 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1dU/* scJU */, E(_1dW/* scJY */), _/* EXTERNAL */)),
                                _1dY/* scK8 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, _1dh/* scHS */, E(_1dX/* scK3 */), _/* EXTERNAL */)),
                                _1dZ/* scKd */ = B(_17P/* FormEngine.JQuery.$wa30 */(_1c1/* scDb */, E(_1dY/* scK8 */), _/* EXTERNAL */)),
                                _1e0/* scKi */ = B(_17z/* FormEngine.JQuery.$wa23 */(_1c1/* scDb */, E(_1dZ/* scKd */), _/* EXTERNAL */)),
                                _1e1/* scKn */ = B(_185/* FormEngine.JQuery.$wa31 */(_1cU/* scGJ */, E(_1e0/* scKi */), _/* EXTERNAL */)),
                                _1e2/* scKq */ = function(_/* EXTERNAL */, _1e3/* scKs */){
                                  var _1e4/* scKt */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, _1e3/* scKs */, _/* EXTERNAL */)),
                                  _1e5/* scKy */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1dU/* scJU */, E(_1e4/* scKt */), _/* EXTERNAL */));
                                  return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aN/* FormEngine.FormElement.Rendering.lvl40 */, _1e5/* scKy */, _/* EXTERNAL */);});
                                };
                                if(!B(_IO/* GHC.Base.eqString */(_1dL/* scJI */, _1dU/* scJU */))){
                                  var _1e6/* scKE */ = B(_1e2/* scKq */(_/* EXTERNAL */, E(_1e1/* scKn */)));
                                  _1dO/*  scJQ */ = _1dV/* scJV */;
                                  _1dP/*  scJR */ = _1e6/* scKE */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1e7/* scKJ */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1e1/* scKn */), _/* EXTERNAL */)),
                                  _1e8/* scKO */ = B(_1e2/* scKq */(_/* EXTERNAL */, E(_1e7/* scKJ */)));
                                  _1dO/*  scJQ */ = _1dV/* scJV */;
                                  _1dP/*  scJR */ = _1e8/* scKO */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1dO/*  scJQ */, _1dP/*  scJR */, _/* EXTERNAL */));
                            if(_1dQ/*  scJP */!=__continue/* EXTERNAL */){
                              return _1dQ/*  scJP */;
                            }
                          }
                        };
                        return new F(function(){return _1dN/* scJP */(_1dk/* scI6 */, _1dM/* scJM */, _/* EXTERNAL */);});
                      }else{
                        var _1e9/* scKT */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1dq/* scIy */), _/* EXTERNAL */)),
                        _1ea/* scKY */ = B(_1dr/* scIB */(_/* EXTERNAL */, E(_1e9/* scKT */))),
                        _1eb/* scL1 */ = function(_1ec/*  scL2 */, _1ed/*  scL3 */, _/* EXTERNAL */){
                          while(1){
                            var _1ee/*  scL1 */ = B((function(_1ef/* scL2 */, _1eg/* scL3 */, _/* EXTERNAL */){
                              var _1eh/* scL5 */ = E(_1ef/* scL2 */);
                              if(!_1eh/* scL5 */._){
                                return _1eg/* scL3 */;
                              }else{
                                var _1ei/* scL6 */ = _1eh/* scL5 */.a,
                                _1ej/* scL7 */ = _1eh/* scL5 */.b,
                                _1ek/* scLa */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl38 */, E(_1eg/* scL3 */), _/* EXTERNAL */)),
                                _1el/* scLf */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1ei/* scL6 */, E(_1ek/* scLa */), _/* EXTERNAL */)),
                                _1em/* scLk */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, _1dh/* scHS */, E(_1el/* scLf */), _/* EXTERNAL */)),
                                _1en/* scLp */ = B(_17P/* FormEngine.JQuery.$wa30 */(_1c1/* scDb */, E(_1em/* scLk */), _/* EXTERNAL */)),
                                _1eo/* scLu */ = B(_17z/* FormEngine.JQuery.$wa23 */(_1c1/* scDb */, E(_1en/* scLp */), _/* EXTERNAL */)),
                                _1ep/* scLz */ = B(_185/* FormEngine.JQuery.$wa31 */(_1cU/* scGJ */, E(_1eo/* scLu */), _/* EXTERNAL */)),
                                _1eq/* scLC */ = function(_/* EXTERNAL */, _1er/* scLE */){
                                  var _1es/* scLF */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, _1er/* scLE */, _/* EXTERNAL */)),
                                  _1et/* scLK */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1ei/* scL6 */, E(_1es/* scLF */), _/* EXTERNAL */));
                                  return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aN/* FormEngine.FormElement.Rendering.lvl40 */, _1et/* scLK */, _/* EXTERNAL */);});
                                };
                                if(!B(_IO/* GHC.Base.eqString */(_1dL/* scJI */, _1ei/* scL6 */))){
                                  var _1eu/* scLQ */ = B(_1eq/* scLC */(_/* EXTERNAL */, E(_1ep/* scLz */)));
                                  _1ec/*  scL2 */ = _1ej/* scL7 */;
                                  _1ed/*  scL3 */ = _1eu/* scLQ */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1ev/* scLV */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1ep/* scLz */), _/* EXTERNAL */)),
                                  _1ew/* scM0 */ = B(_1eq/* scLC */(_/* EXTERNAL */, E(_1ev/* scLV */)));
                                  _1ec/*  scL2 */ = _1ej/* scL7 */;
                                  _1ed/*  scL3 */ = _1ew/* scM0 */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1ec/*  scL2 */, _1ed/*  scL3 */, _/* EXTERNAL */));
                            if(_1ee/*  scL1 */!=__continue/* EXTERNAL */){
                              return _1ee/*  scL1 */;
                            }
                          }
                        };
                        return new F(function(){return _1eb/* scL1 */(_1dk/* scI6 */, _1ea/* scKY */, _/* EXTERNAL */);});
                      }
                    }
                  }
                  break;
                default:
                  return _1de/* scHI */;
              }
            }else{
              return E(_16D/* FormEngine.FormItem.nfiUnit1 */);
            }
          },
          _1ex/* scM3 */ = E(_1c3/* scDe */.b);
          if(!_1ex/* scM3 */._){
            var _1ey/* scM4 */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _I/* GHC.Types.[] */, _1d3/* scHe */, _/* EXTERNAL */));
            return new F(function(){return _1d4/* scHf */(_/* EXTERNAL */, _1ey/* scM4 */);});
          }else{
            var _1ez/* scM9 */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, B(_4w/* GHC.Show.$fShowInt_$cshow */(_1ex/* scM3 */.a)), _1d3/* scHe */, _/* EXTERNAL */));
            return new F(function(){return _1d4/* scHf */(_/* EXTERNAL */, _1ez/* scM9 */);});
          }
        },
        _1eA/* scMc */ = E(_1cY/* scGQ */.c);
        if(!_1eA/* scMc */._){
          var _1eB/* scMf */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1d1/* scH9 */), _/* EXTERNAL */));
          return new F(function(){return _1d2/* scHc */(_/* EXTERNAL */, E(_1eB/* scMf */));});
        }else{
          var _1eC/* scMn */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1eA/* scMc */.a, E(_1d1/* scH9 */), _/* EXTERNAL */));
          return new F(function(){return _1d2/* scHc */(_/* EXTERNAL */, E(_1eC/* scMn */));});
        }
      };
      return new F(function(){return _18X/* FormEngine.FormElement.Rendering.$wa2 */(_1cW/* scMs */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */);});
      break;
    case 5:
      var _1eD/* scMt */ = _1c3/* scDe */.a,
      _1eE/* scMu */ = _1c3/* scDe */.b,
      _1eF/* scMw */ = new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1eD/* scMt */)).b));
      }),
      _1eG/* scMJ */ = new T(function(){
        var _1eH/* scMU */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1eD/* scMt */)).c);
        if(!_1eH/* scMU */._){
          return __Z/* EXTERNAL */;
        }else{
          return E(_1eH/* scMU */.a);
        }
      }),
      _1eI/* scMW */ = function(_1eJ/* scMX */, _/* EXTERNAL */){
        var _1eK/* scMZ */ = B(_1a8/* FormEngine.JQuery.isRadioSelected1 */(_1eF/* scMw */, _/* EXTERNAL */));
        return new F(function(){return _15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1c3/* scDe */, _1bY/* scD7 */, _1eK/* scMZ */, _/* EXTERNAL */);});
      },
      _1eL/* scN2 */ = new T(function(){
        return B(_1a2/* FormEngine.FormElement.Rendering.go */(_1eE/* scMu */, _1aj/* GHC.List.last1 */));
      }),
      _1eM/* scN3 */ = function(_1eN/* scN4 */, _/* EXTERNAL */){
        return new F(function(){return _50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1av/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
          return B(_12/* GHC.Base.++ */(B(_1bO/* FormEngine.FormElement.Identifiers.radioId */(_1c3/* scDe */, _1eN/* scN4 */)), _1bu/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
        },1))), _/* EXTERNAL */);});
      },
      _1eO/* scN9 */ = function(_1eP/* scNa */, _/* EXTERNAL */){
        while(1){
          var _1eQ/* scNc */ = E(_1eP/* scNa */);
          if(!_1eQ/* scNc */._){
            return _I/* GHC.Types.[] */;
          }else{
            var _1eR/* scNe */ = _1eQ/* scNc */.b,
            _1eS/* scNf */ = E(_1eQ/* scNc */.a);
            if(!_1eS/* scNf */._){
              _1eP/* scNa */ = _1eR/* scNe */;
              continue;
            }else{
              var _1eT/* scNl */ = B(_1eM/* scN3 */(_1eS/* scNf */, _/* EXTERNAL */)),
              _1eU/* scNo */ = B(_1eO/* scN9 */(_1eR/* scNe */, _/* EXTERNAL */));
              return new T2(1,_1eT/* scNl */,_1eU/* scNo */);
            }
          }
        }
      },
      _1eV/* scQ1 */ = function(_/* EXTERNAL */){
        var _1eW/* scNt */ = B(_50/* FormEngine.JQuery.select1 */(_1aM/* FormEngine.FormElement.Rendering.lvl39 */, _/* EXTERNAL */)),
        _1eX/* scNw */ = function(_1eY/*  scNx */, _1eZ/*  scNy */, _/* EXTERNAL */){
          while(1){
            var _1f0/*  scNw */ = B((function(_1f1/* scNx */, _1f2/* scNy */, _/* EXTERNAL */){
              var _1f3/* scNA */ = E(_1f1/* scNx */);
              if(!_1f3/* scNA */._){
                return _1f2/* scNy */;
              }else{
                var _1f4/* scNB */ = _1f3/* scNA */.a,
                _1f5/* scNC */ = _1f3/* scNA */.b,
                _1f6/* scNF */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl38 */, E(_1f2/* scNy */), _/* EXTERNAL */)),
                _1f7/* scNL */ = B(_HR/* FormEngine.JQuery.$wa20 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_1bO/* FormEngine.FormElement.Identifiers.radioId */(_1c3/* scDe */, _1f4/* scNB */));
                },1), E(_1f6/* scNF */), _/* EXTERNAL */)),
                _1f8/* scNQ */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, _1eF/* scMw */, E(_1f7/* scNL */), _/* EXTERNAL */)),
                _1f9/* scNV */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1eG/* scMJ */, E(_1f8/* scNQ */), _/* EXTERNAL */)),
                _1fa/* scO1 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
                  return B(_1bp/* FormEngine.FormElement.FormElement.optionElemValue */(_1f4/* scNB */));
                },1), E(_1f9/* scNV */), _/* EXTERNAL */)),
                _1fb/* scO4 */ = function(_/* EXTERNAL */, _1fc/* scO6 */){
                  var _1fd/* scOA */ = B(_17z/* FormEngine.JQuery.$wa23 */(function(_1fe/* scO7 */, _/* EXTERNAL */){
                    var _1ff/* scO9 */ = B(_1eO/* scN9 */(_1eE/* scMu */, _/* EXTERNAL */)),
                    _1fg/* scOc */ = B(_19N/* FormEngine.FormElement.Rendering.a5 */(_1ff/* scO9 */, _/* EXTERNAL */)),
                    _1fh/* scOf */ = E(_1f4/* scNB */);
                    if(!_1fh/* scOf */._){
                      var _1fi/* scOi */ = B(_1a8/* FormEngine.JQuery.isRadioSelected1 */(_1eF/* scMw */, _/* EXTERNAL */));
                      return new F(function(){return _15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1c3/* scDe */, _1bY/* scD7 */, _1fi/* scOi */, _/* EXTERNAL */);});
                    }else{
                      var _1fj/* scOo */ = B(_1eM/* scN3 */(_1fh/* scOf */, _/* EXTERNAL */)),
                      _1fk/* scOt */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _IM/* FormEngine.JQuery.appearJq2 */, E(_1fj/* scOo */), _/* EXTERNAL */)),
                      _1fl/* scOw */ = B(_1a8/* FormEngine.JQuery.isRadioSelected1 */(_1eF/* scMw */, _/* EXTERNAL */));
                      return new F(function(){return _15q/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1c3/* scDe */, _1bY/* scD7 */, _1fl/* scOw */, _/* EXTERNAL */);});
                    }
                  }, _1fc/* scO6 */, _/* EXTERNAL */)),
                  _1fm/* scOF */ = B(_185/* FormEngine.JQuery.$wa31 */(_1eI/* scMW */, E(_1fd/* scOA */), _/* EXTERNAL */)),
                  _1fn/* scOK */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18k/* FormEngine.FormElement.Rendering.lvl1 */, E(_1fm/* scOF */), _/* EXTERNAL */)),
                  _1fo/* scOQ */ = B(_Ib/* FormEngine.JQuery.$wa34 */(new T(function(){
                    return B(_1bp/* FormEngine.FormElement.FormElement.optionElemValue */(_1f4/* scNB */));
                  },1), E(_1fn/* scOK */), _/* EXTERNAL */)),
                  _1fp/* scOT */ = E(_1f4/* scNB */);
                  if(!_1fp/* scOT */._){
                    var _1fq/* scOU */ = _1fp/* scOT */.a,
                    _1fr/* scOY */ = B(_I6/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1fo/* scOQ */), _/* EXTERNAL */)),
                    _1fs/* scP1 */ = E(_1eL/* scN2 */);
                    if(!_1fs/* scP1 */._){
                      if(!B(_Lw/* FormEngine.FormItem.$fEqOption_$c== */(_1fq/* scOU */, _1fs/* scP1 */.a))){
                        return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aK/* FormEngine.FormElement.Rendering.lvl37 */, _1fr/* scOY */, _/* EXTERNAL */);});
                      }else{
                        return _1fr/* scOY */;
                      }
                    }else{
                      if(!B(_Lw/* FormEngine.FormItem.$fEqOption_$c== */(_1fq/* scOU */, _1fs/* scP1 */.a))){
                        return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aK/* FormEngine.FormElement.Rendering.lvl37 */, _1fr/* scOY */, _/* EXTERNAL */);});
                      }else{
                        return _1fr/* scOY */;
                      }
                    }
                  }else{
                    var _1ft/* scP9 */ = _1fp/* scOT */.a,
                    _1fu/* scPe */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1au/* FormEngine.FormElement.Rendering.lvl21 */, E(_1fo/* scOQ */), _/* EXTERNAL */)),
                    _1fv/* scPh */ = E(_1eL/* scN2 */);
                    if(!_1fv/* scPh */._){
                      if(!B(_Lw/* FormEngine.FormItem.$fEqOption_$c== */(_1ft/* scP9 */, _1fv/* scPh */.a))){
                        return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aK/* FormEngine.FormElement.Rendering.lvl37 */, _1fu/* scPe */, _/* EXTERNAL */);});
                      }else{
                        return _1fu/* scPe */;
                      }
                    }else{
                      if(!B(_Lw/* FormEngine.FormItem.$fEqOption_$c== */(_1ft/* scP9 */, _1fv/* scPh */.a))){
                        return new F(function(){return _19R/* FormEngine.JQuery.appendT1 */(_1aK/* FormEngine.FormElement.Rendering.lvl37 */, _1fu/* scPe */, _/* EXTERNAL */);});
                      }else{
                        return _1fu/* scPe */;
                      }
                    }
                  }
                },
                _1fw/* scPp */ = E(_1f4/* scNB */);
                if(!_1fw/* scPp */._){
                  if(!E(_1fw/* scPp */.b)){
                    var _1fx/* scPv */ = B(_1fb/* scO4 */(_/* EXTERNAL */, E(_1fa/* scO1 */)));
                    _1eY/*  scNx */ = _1f5/* scNC */;
                    _1eZ/*  scNy */ = _1fx/* scPv */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1fy/* scPA */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1fa/* scO1 */), _/* EXTERNAL */)),
                    _1fz/* scPF */ = B(_1fb/* scO4 */(_/* EXTERNAL */, E(_1fy/* scPA */)));
                    _1eY/*  scNx */ = _1f5/* scNC */;
                    _1eZ/*  scNy */ = _1fz/* scPF */;
                    return __continue/* EXTERNAL */;
                  }
                }else{
                  if(!E(_1fw/* scPp */.b)){
                    var _1fA/* scPO */ = B(_1fb/* scO4 */(_/* EXTERNAL */, E(_1fa/* scO1 */)));
                    _1eY/*  scNx */ = _1f5/* scNC */;
                    _1eZ/*  scNy */ = _1fA/* scPO */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1fB/* scPT */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1fa/* scO1 */), _/* EXTERNAL */)),
                    _1fC/* scPY */ = B(_1fb/* scO4 */(_/* EXTERNAL */, E(_1fB/* scPT */)));
                    _1eY/*  scNx */ = _1f5/* scNC */;
                    _1eZ/*  scNy */ = _1fC/* scPY */;
                    return __continue/* EXTERNAL */;
                  }
                }
              }
            })(_1eY/*  scNx */, _1eZ/*  scNy */, _/* EXTERNAL */));
            if(_1f0/*  scNw */!=__continue/* EXTERNAL */){
              return _1f0/*  scNw */;
            }
          }
        };
        return new F(function(){return _1eX/* scNw */(_1eE/* scMu */, _1eW/* scNt */, _/* EXTERNAL */);});
      },
      _1fD/* scQ2 */ = B(_18X/* FormEngine.FormElement.Rendering.$wa2 */(_1eV/* scQ1 */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */)),
      _1fE/* scQ5 */ = function(_1fF/* scQ6 */, _1fG/* scQ7 */, _/* EXTERNAL */){
        while(1){
          var _1fH/* scQ9 */ = E(_1fF/* scQ6 */);
          if(!_1fH/* scQ9 */._){
            return _1fG/* scQ7 */;
          }else{
            var _1fI/* scQc */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1fH/* scQ9 */.a, _1bY/* scD7 */, _1bZ/* scD8 */, _1fG/* scQ7 */, _/* EXTERNAL */));
            _1fF/* scQ6 */ = _1fH/* scQ9 */.b;
            _1fG/* scQ7 */ = _1fI/* scQc */;
            continue;
          }
        }
      },
      _1fJ/* scQf */ = function(_1fK/*  scQg */, _1fL/*  scQh */, _/* EXTERNAL */){
        while(1){
          var _1fM/*  scQf */ = B((function(_1fN/* scQg */, _1fO/* scQh */, _/* EXTERNAL */){
            var _1fP/* scQj */ = E(_1fN/* scQg */);
            if(!_1fP/* scQj */._){
              return _1fO/* scQh */;
            }else{
              var _1fQ/* scQl */ = _1fP/* scQj */.b,
              _1fR/* scQm */ = E(_1fP/* scQj */.a);
              if(!_1fR/* scQm */._){
                var _1fS/*   scQh */ = _1fO/* scQh */;
                _1fK/*  scQg */ = _1fQ/* scQl */;
                _1fL/*  scQh */ = _1fS/*   scQh */;
                return __continue/* EXTERNAL */;
              }else{
                var _1fT/* scQu */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aJ/* FormEngine.FormElement.Rendering.lvl36 */, E(_1fO/* scQh */), _/* EXTERNAL */)),
                _1fU/* scQB */ = B(_HR/* FormEngine.JQuery.$wa20 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_1bO/* FormEngine.FormElement.Identifiers.radioId */(_1c3/* scDe */, _1fR/* scQm */)), _1bu/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                },1), E(_1fT/* scQu */), _/* EXTERNAL */)),
                _1fV/* scQG */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
                _1fW/* scQJ */ = __app1/* EXTERNAL */(_1fV/* scQG */, E(_1fU/* scQB */)),
                _1fX/* scQM */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
                _1fY/* scQP */ = __app1/* EXTERNAL */(_1fX/* scQM */, _1fW/* scQJ */),
                _1fZ/* scQS */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, _1fY/* scQP */, _/* EXTERNAL */)),
                _1g0/* scQV */ = B(_1fE/* scQ5 */(_1fR/* scQm */.c, _1fZ/* scQS */, _/* EXTERNAL */)),
                _1g1/* scR0 */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
                _1g2/* scR3 */ = __app1/* EXTERNAL */(_1g1/* scR0 */, E(_1g0/* scQV */)),
                _1g3/* scR6 */ = function(_1g4/*  scR7 */, _1g5/*  scR8 */, _1g6/*  sbSp */, _/* EXTERNAL */){
                  while(1){
                    var _1g7/*  scR6 */ = B((function(_1g8/* scR7 */, _1g9/* scR8 */, _1ga/* sbSp */, _/* EXTERNAL */){
                      var _1gb/* scRa */ = E(_1g8/* scR7 */);
                      if(!_1gb/* scRa */._){
                        return _1g9/* scR8 */;
                      }else{
                        var _1gc/* scRd */ = _1gb/* scRa */.b,
                        _1gd/* scRe */ = E(_1gb/* scRa */.a);
                        if(!_1gd/* scRe */._){
                          var _1ge/*   scR8 */ = _1g9/* scR8 */,
                          _1gf/*   sbSp */ = _/* EXTERNAL */;
                          _1g4/*  scR7 */ = _1gc/* scRd */;
                          _1g5/*  scR8 */ = _1ge/*   scR8 */;
                          _1g6/*  sbSp */ = _1gf/*   sbSp */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _1gg/* scRk */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aJ/* FormEngine.FormElement.Rendering.lvl36 */, _1g9/* scR8 */, _/* EXTERNAL */)),
                          _1gh/* scRr */ = B(_HR/* FormEngine.JQuery.$wa20 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                            return B(_12/* GHC.Base.++ */(B(_1bO/* FormEngine.FormElement.Identifiers.radioId */(_1c3/* scDe */, _1gd/* scRe */)), _1bu/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                          },1), E(_1gg/* scRk */), _/* EXTERNAL */)),
                          _1gi/* scRx */ = __app1/* EXTERNAL */(_1fV/* scQG */, E(_1gh/* scRr */)),
                          _1gj/* scRB */ = __app1/* EXTERNAL */(_1fX/* scQM */, _1gi/* scRx */),
                          _1gk/* scRE */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, _1gj/* scRB */, _/* EXTERNAL */)),
                          _1gl/* scRH */ = B(_1fE/* scQ5 */(_1gd/* scRe */.c, _1gk/* scRE */, _/* EXTERNAL */)),
                          _1gm/* scRN */ = __app1/* EXTERNAL */(_1g1/* scR0 */, E(_1gl/* scRH */)),
                          _1gf/*   sbSp */ = _/* EXTERNAL */;
                          _1g4/*  scR7 */ = _1gc/* scRd */;
                          _1g5/*  scR8 */ = _1gm/* scRN */;
                          _1g6/*  sbSp */ = _1gf/*   sbSp */;
                          return __continue/* EXTERNAL */;
                        }
                      }
                    })(_1g4/*  scR7 */, _1g5/*  scR8 */, _1g6/*  sbSp */, _/* EXTERNAL */));
                    if(_1g7/*  scR6 */!=__continue/* EXTERNAL */){
                      return _1g7/*  scR6 */;
                    }
                  }
                };
                return new F(function(){return _1g3/* scR6 */(_1fQ/* scQl */, _1g2/* scR3 */, _/* EXTERNAL */, _/* EXTERNAL */);});
              }
            }
          })(_1fK/*  scQg */, _1fL/*  scQh */, _/* EXTERNAL */));
          if(_1fM/*  scQf */!=__continue/* EXTERNAL */){
            return _1fM/*  scQf */;
          }
        }
      };
      return new F(function(){return _1fJ/* scQf */(_1eE/* scMu */, _1fD/* scQ2 */, _/* EXTERNAL */);});
      break;
    case 6:
      var _1gn/* scRQ */ = _1c3/* scDe */.a,
      _1go/* scUI */ = function(_/* EXTERNAL */){
        var _1gp/* scRW */ = B(_50/* FormEngine.JQuery.select1 */(_1aI/* FormEngine.FormElement.Rendering.lvl35 */, _/* EXTERNAL */)),
        _1gq/* scRZ */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1gn/* scRQ */)),
        _1gr/* scSc */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, B(_4M/* FormEngine.FormItem.numbering2text */(_1gq/* scRZ */.b)), E(_1gp/* scRW */), _/* EXTERNAL */)),
        _1gs/* scSf */ = function(_/* EXTERNAL */, _1gt/* scSh */){
          var _1gu/* scSl */ = B(_1aW/* FormEngine.JQuery.onBlur1 */(function(_1gv/* scSi */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1gt/* scSh */, _/* EXTERNAL */)),
          _1gw/* scSr */ = B(_1b6/* FormEngine.JQuery.onChange1 */(function(_1gx/* scSo */, _/* EXTERNAL */){
            return new F(function(){return _17k/* FormEngine.FormElement.Rendering.$wa1 */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1gu/* scSl */, _/* EXTERNAL */)),
          _1gy/* scSx */ = B(_17W/* FormEngine.JQuery.onMouseLeave1 */(function(_1gz/* scSu */, _/* EXTERNAL */){
            return new F(function(){return _17c/* FormEngine.FormElement.Rendering.$wa */(_1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, _/* EXTERNAL */);});
          }, _1gw/* scSr */, _/* EXTERNAL */)),
          _1gA/* scSA */ = E(_1gn/* scRQ */);
          if(_1gA/* scSA */._==5){
            var _1gB/* scSE */ = E(_1gA/* scSA */.b);
            if(!_1gB/* scSE */._){
              return _1gy/* scSx */;
            }else{
              var _1gC/* scSG */ = _1gB/* scSE */.b,
              _1gD/* scSH */ = E(_1gB/* scSE */.a),
              _1gE/* scSI */ = _1gD/* scSH */.a,
              _1gF/* scSM */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl33 */, E(_1gy/* scSx */), _/* EXTERNAL */)),
              _1gG/* scSR */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1gE/* scSI */, E(_1gF/* scSM */), _/* EXTERNAL */)),
              _1gH/* scSW */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1gD/* scSH */.b, E(_1gG/* scSR */), _/* EXTERNAL */)),
              _1gI/* scSZ */ = E(_1c3/* scDe */.b);
              if(!_1gI/* scSZ */._){
                var _1gJ/* scT0 */ = function(_1gK/* scT1 */, _1gL/* scT2 */, _/* EXTERNAL */){
                  while(1){
                    var _1gM/* scT4 */ = E(_1gK/* scT1 */);
                    if(!_1gM/* scT4 */._){
                      return _1gL/* scT2 */;
                    }else{
                      var _1gN/* scT7 */ = E(_1gM/* scT4 */.a),
                      _1gO/* scTc */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl33 */, E(_1gL/* scT2 */), _/* EXTERNAL */)),
                      _1gP/* scTh */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1gN/* scT7 */.a, E(_1gO/* scTc */), _/* EXTERNAL */)),
                      _1gQ/* scTm */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1gN/* scT7 */.b, E(_1gP/* scTh */), _/* EXTERNAL */));
                      _1gK/* scT1 */ = _1gM/* scT4 */.b;
                      _1gL/* scT2 */ = _1gQ/* scTm */;
                      continue;
                    }
                  }
                };
                return new F(function(){return _1gJ/* scT0 */(_1gC/* scSG */, _1gH/* scSW */, _/* EXTERNAL */);});
              }else{
                var _1gR/* scTp */ = _1gI/* scSZ */.a;
                if(!B(_IO/* GHC.Base.eqString */(_1gE/* scSI */, _1gR/* scTp */))){
                  var _1gS/* scTr */ = function(_1gT/* scTs */, _1gU/* scTt */, _/* EXTERNAL */){
                    while(1){
                      var _1gV/* scTv */ = E(_1gT/* scTs */);
                      if(!_1gV/* scTv */._){
                        return _1gU/* scTt */;
                      }else{
                        var _1gW/* scTx */ = _1gV/* scTv */.b,
                        _1gX/* scTy */ = E(_1gV/* scTv */.a),
                        _1gY/* scTz */ = _1gX/* scTy */.a,
                        _1gZ/* scTD */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl33 */, E(_1gU/* scTt */), _/* EXTERNAL */)),
                        _1h0/* scTI */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1gY/* scTz */, E(_1gZ/* scTD */), _/* EXTERNAL */)),
                        _1h1/* scTN */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1gX/* scTy */.b, E(_1h0/* scTI */), _/* EXTERNAL */));
                        if(!B(_IO/* GHC.Base.eqString */(_1gY/* scTz */, _1gR/* scTp */))){
                          _1gT/* scTs */ = _1gW/* scTx */;
                          _1gU/* scTt */ = _1h1/* scTN */;
                          continue;
                        }else{
                          var _1h2/* scTT */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aF/* FormEngine.FormElement.Rendering.lvl32 */, _1aF/* FormEngine.FormElement.Rendering.lvl32 */, E(_1h1/* scTN */), _/* EXTERNAL */));
                          _1gT/* scTs */ = _1gW/* scTx */;
                          _1gU/* scTt */ = _1h2/* scTT */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1gS/* scTr */(_1gC/* scSG */, _1gH/* scSW */, _/* EXTERNAL */);});
                }else{
                  var _1h3/* scTY */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aF/* FormEngine.FormElement.Rendering.lvl32 */, _1aF/* FormEngine.FormElement.Rendering.lvl32 */, E(_1gH/* scSW */), _/* EXTERNAL */)),
                  _1h4/* scU1 */ = function(_1h5/* scU2 */, _1h6/* scU3 */, _/* EXTERNAL */){
                    while(1){
                      var _1h7/* scU5 */ = E(_1h5/* scU2 */);
                      if(!_1h7/* scU5 */._){
                        return _1h6/* scU3 */;
                      }else{
                        var _1h8/* scU7 */ = _1h7/* scU5 */.b,
                        _1h9/* scU8 */ = E(_1h7/* scU5 */.a),
                        _1ha/* scU9 */ = _1h9/* scU8 */.a,
                        _1hb/* scUd */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl33 */, E(_1h6/* scU3 */), _/* EXTERNAL */)),
                        _1hc/* scUi */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, _1ha/* scU9 */, E(_1hb/* scUd */), _/* EXTERNAL */)),
                        _1hd/* scUn */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1h9/* scU8 */.b, E(_1hc/* scUi */), _/* EXTERNAL */));
                        if(!B(_IO/* GHC.Base.eqString */(_1ha/* scU9 */, _1gR/* scTp */))){
                          _1h5/* scU2 */ = _1h8/* scU7 */;
                          _1h6/* scU3 */ = _1hd/* scUn */;
                          continue;
                        }else{
                          var _1he/* scUt */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aF/* FormEngine.FormElement.Rendering.lvl32 */, _1aF/* FormEngine.FormElement.Rendering.lvl32 */, E(_1hd/* scUn */), _/* EXTERNAL */));
                          _1h5/* scU2 */ = _1h8/* scU7 */;
                          _1h6/* scU3 */ = _1he/* scUt */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1h4/* scU1 */(_1gC/* scSG */, _1h3/* scTY */, _/* EXTERNAL */);});
                }
              }
            }
          }else{
            return E(_1ak/* FormEngine.FormItem.lfiAvailableOptions1 */);
          }
        },
        _1hf/* scUw */ = E(_1gq/* scRZ */.c);
        if(!_1hf/* scUw */._){
          var _1hg/* scUz */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1gr/* scSc */), _/* EXTERNAL */));
          return new F(function(){return _1gs/* scSf */(_/* EXTERNAL */, _1hg/* scUz */);});
        }else{
          var _1hh/* scUF */ = B(_HJ/* FormEngine.JQuery.$wa6 */(_1aH/* FormEngine.FormElement.Rendering.lvl34 */, _1hf/* scUw */.a, E(_1gr/* scSc */), _/* EXTERNAL */));
          return new F(function(){return _1gs/* scSf */(_/* EXTERNAL */, _1hh/* scUF */);});
        }
      };
      return new F(function(){return _18X/* FormEngine.FormElement.Rendering.$wa2 */(_1go/* scUI */, _1c3/* scDe */, _1bY/* scD7 */, _1bZ/* scD8 */, E(_1c0/* scD9 */), _/* EXTERNAL */);});
      break;
    case 7:
      var _1hi/* scUJ */ = _1c3/* scDe */.a,
      _1hj/* scUK */ = _1c3/* scDe */.b,
      _1hk/* scUO */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aE/* FormEngine.FormElement.Rendering.lvl31 */, E(_1c0/* scD9 */), _/* EXTERNAL */)),
      _1hl/* scUT */ = new T(function(){
        var _1hm/* scUU */ = E(_1hi/* scUJ */);
        switch(_1hm/* scUU */._){
          case 7:
            return E(_1hm/* scUU */.b);
            break;
          case 8:
            return E(_1hm/* scUU */.b);
            break;
          case 9:
            return E(_1hm/* scUU */.b);
            break;
          default:
            return E(_5O/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _1hn/* scV5 */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1az/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_4w/* GHC.Show.$fShowInt_$cshow */(_1hl/* scUT */));
      },1), E(_1hk/* scUO */), _/* EXTERNAL */)),
      _1ho/* scV8 */ = E(_1hl/* scUT */),
      _1hp/* scVa */ = function(_/* EXTERNAL */, _1hq/* scVc */){
        var _1hr/* scVg */ = __app1/* EXTERNAL */(E(_HQ/* FormEngine.JQuery.addClassInside_f3 */), _1hq/* scVc */),
        _1hs/* scVm */ = __app1/* EXTERNAL */(E(_HP/* FormEngine.JQuery.addClassInside_f2 */), _1hr/* scVg */),
        _1ht/* scVp */ = B(_4q/* FormEngine.FormItem.fiDescriptor */(_1hi/* scUJ */)),
        _1hu/* scVu */ = _1ht/* scVp */.e,
        _1hv/* scVz */ = E(_1ht/* scVp */.a);
        if(!_1hv/* scVz */._){
          var _1hw/* scVA */ = function(_/* EXTERNAL */, _1hx/* scVC */){
            var _1hy/* scVD */ = function(_1hz/* scVE */, _1hA/* scVF */, _/* EXTERNAL */){
              while(1){
                var _1hB/* scVH */ = E(_1hz/* scVE */);
                if(!_1hB/* scVH */._){
                  return _1hA/* scVF */;
                }else{
                  var _1hC/* scVK */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1hB/* scVH */.a, _1bY/* scD7 */, _1bZ/* scD8 */, _1hA/* scVF */, _/* EXTERNAL */));
                  _1hz/* scVE */ = _1hB/* scVH */.b;
                  _1hA/* scVF */ = _1hC/* scVK */;
                  continue;
                }
              }
            },
            _1hD/* scVN */ = B(_1hy/* scVD */(_1hj/* scUK */, _1hx/* scVC */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_HO/* FormEngine.JQuery.addClassInside_f1 */), E(_1hD/* scVN */));});
          },
          _1hE/* scVZ */ = E(_1hu/* scVu */);
          if(!_1hE/* scVZ */._){
            return new F(function(){return _1hw/* scVA */(_/* EXTERNAL */, _1hs/* scVm */);});
          }else{
            var _1hF/* scW2 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18b/* FormEngine.FormElement.Rendering.lvl */, _1hs/* scVm */, _/* EXTERNAL */)),
            _1hG/* scW7 */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1hE/* scVZ */.a, E(_1hF/* scW2 */), _/* EXTERNAL */));
            return new F(function(){return _1hw/* scVA */(_/* EXTERNAL */, _1hG/* scW7 */);});
          }
        }else{
          var _1hH/* scWe */ = B(_I6/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_1aC/* FormEngine.FormElement.Rendering.lvl29 */, new T(function(){
            return B(_12/* GHC.Base.++ */(B(_4e/* GHC.Show.$wshowSignedInt */(0, _1ho/* scV8 */, _I/* GHC.Types.[] */)), _1aB/* FormEngine.FormElement.Rendering.lvl28 */));
          },1))), _1hs/* scVm */, _/* EXTERNAL */)),
          _1hI/* scWj */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1hv/* scVz */.a, E(_1hH/* scWe */), _/* EXTERNAL */)),
          _1hJ/* scWm */ = function(_/* EXTERNAL */, _1hK/* scWo */){
            var _1hL/* scWp */ = function(_1hM/* scWq */, _1hN/* scWr */, _/* EXTERNAL */){
              while(1){
                var _1hO/* scWt */ = E(_1hM/* scWq */);
                if(!_1hO/* scWt */._){
                  return _1hN/* scWr */;
                }else{
                  var _1hP/* scWw */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1hO/* scWt */.a, _1bY/* scD7 */, _1bZ/* scD8 */, _1hN/* scWr */, _/* EXTERNAL */));
                  _1hM/* scWq */ = _1hO/* scWt */.b;
                  _1hN/* scWr */ = _1hP/* scWw */;
                  continue;
                }
              }
            },
            _1hQ/* scWz */ = B(_1hL/* scWp */(_1hj/* scUK */, _1hK/* scWo */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_HO/* FormEngine.JQuery.addClassInside_f1 */), E(_1hQ/* scWz */));});
          },
          _1hR/* scWL */ = E(_1hu/* scVu */);
          if(!_1hR/* scWL */._){
            return new F(function(){return _1hJ/* scWm */(_/* EXTERNAL */, _1hI/* scWj */);});
          }else{
            var _1hS/* scWP */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18b/* FormEngine.FormElement.Rendering.lvl */, E(_1hI/* scWj */), _/* EXTERNAL */)),
            _1hT/* scWU */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1hR/* scWL */.a, E(_1hS/* scWP */), _/* EXTERNAL */));
            return new F(function(){return _1hJ/* scWm */(_/* EXTERNAL */, _1hT/* scWU */);});
          }
        }
      };
      if(_1ho/* scV8 */<=1){
        return new F(function(){return _1hp/* scVa */(_/* EXTERNAL */, E(_1hn/* scV5 */));});
      }else{
        var _1hU/* scX3 */ = B(_17s/* FormEngine.JQuery.$wa1 */(_1aD/* FormEngine.FormElement.Rendering.lvl30 */, E(_1hn/* scV5 */), _/* EXTERNAL */));
        return new F(function(){return _1hp/* scVa */(_/* EXTERNAL */, E(_1hU/* scX3 */));});
      }
      break;
    case 8:
      var _1hV/* scX8 */ = _1c3/* scDe */.a,
      _1hW/* scXa */ = _1c3/* scDe */.c,
      _1hX/* scXe */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1aA/* FormEngine.FormElement.Rendering.lvl27 */, E(_1c0/* scD9 */), _/* EXTERNAL */)),
      _1hY/* scXA */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1az/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        var _1hZ/* scXj */ = E(_1hV/* scX8 */);
        switch(_1hZ/* scXj */._){
          case 7:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1hZ/* scXj */.b), _I/* GHC.Types.[] */));
            break;
          case 8:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1hZ/* scXj */.b), _I/* GHC.Types.[] */));
            break;
          case 9:
            return B(_4e/* GHC.Show.$wshowSignedInt */(0, E(_1hZ/* scXj */.b), _I/* GHC.Types.[] */));
            break;
          default:
            return E(_1aU/* FormEngine.FormElement.Rendering.lvl47 */);
        }
      },1), E(_1hX/* scXe */), _/* EXTERNAL */)),
      _1i0/* scXI */ = B(_17P/* FormEngine.JQuery.$wa30 */(function(_1i1/* scXF */, _/* EXTERNAL */){
        return new F(function(){return _18G/* FormEngine.FormElement.Rendering.a4 */(_1c3/* scDe */, _/* EXTERNAL */);});
      }, E(_1hY/* scXA */), _/* EXTERNAL */)),
      _1i2/* scXQ */ = B(_185/* FormEngine.JQuery.$wa31 */(function(_1i3/* scXN */, _/* EXTERNAL */){
        return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a3 */(_1c3/* scDe */, _/* EXTERNAL */);});
      }, E(_1i0/* scXI */), _/* EXTERNAL */)),
      _1i4/* scXV */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
      _1i5/* scXY */ = __app1/* EXTERNAL */(_1i4/* scXV */, E(_1i2/* scXQ */)),
      _1i6/* scY1 */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
      _1i7/* scY4 */ = __app1/* EXTERNAL */(_1i6/* scY1 */, _1i5/* scXY */),
      _1i8/* scY7 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ay/* FormEngine.FormElement.Rendering.lvl25 */, _1i7/* scY4 */, _/* EXTERNAL */)),
      _1i9/* scYn */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1ax/* FormEngine.FormElement.Rendering.lvl24 */, new T(function(){
        return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1hV/* scX8 */)).b));
      },1), E(_1i8/* scY7 */), _/* EXTERNAL */)),
      _1ia/* scYq */ = function(_/* EXTERNAL */, _1ib/* scYs */){
        var _1ic/* scYt */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_1av/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
            return B(_19V/* FormEngine.FormElement.Identifiers.checkboxId */(_1c3/* scDe */));
          },1)));
        }),
        _1id/* scZ0 */ = B(_17z/* FormEngine.JQuery.$wa23 */(function(_1ie/* scYv */, _/* EXTERNAL */){
          var _1if/* scYx */ = B(_50/* FormEngine.JQuery.select1 */(_1ic/* scYt */, _/* EXTERNAL */)),
          _1ig/* scYF */ = __app1/* EXTERNAL */(E(_1bV/* FormEngine.JQuery.target_f1 */), E(_1ie/* scYv */)),
          _1ih/* scYL */ = __app1/* EXTERNAL */(E(_1a6/* FormEngine.JQuery.isChecked_f1 */), _1ig/* scYF */);
          if(!_1ih/* scYL */){
            var _1ii/* scYR */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _Jk/* FormEngine.JQuery.disappearJq2 */, E(_1if/* scYx */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _1ij/* scYW */ = B(_43/* FormEngine.JQuery.$wa2 */(_IN/* FormEngine.JQuery.appearJq3 */, _IM/* FormEngine.JQuery.appearJq2 */, E(_1if/* scYx */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        }, _1ib/* scYs */, _/* EXTERNAL */)),
        _1ik/* scZ3 */ = B(_18n/* FormEngine.FormElement.Rendering.a2 */(_1c3/* scDe */, _1id/* scZ0 */, _/* EXTERNAL */)),
        _1il/* scZ6 */ = function(_/* EXTERNAL */, _1im/* scZ8 */){
          var _1in/* scZj */ = function(_/* EXTERNAL */, _1io/* scZl */){
            var _1ip/* scZm */ = E(_1hW/* scXa */);
            if(!_1ip/* scZm */._){
              return new F(function(){return __app1/* EXTERNAL */(E(_HO/* FormEngine.JQuery.addClassInside_f1 */), _1io/* scZl */);});
            }else{
              var _1iq/* scZw */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1at/* FormEngine.FormElement.Rendering.lvl20 */, _1io/* scZl */, _/* EXTERNAL */)),
              _1ir/* scZC */ = B(_HR/* FormEngine.JQuery.$wa20 */(_18R/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                return B(_19V/* FormEngine.FormElement.Identifiers.checkboxId */(_1c3/* scDe */));
              },1), E(_1iq/* scZw */), _/* EXTERNAL */)),
              _1is/* scZI */ = __app1/* EXTERNAL */(_1i4/* scXV */, E(_1ir/* scZC */)),
              _1it/* scZM */ = __app1/* EXTERNAL */(_1i6/* scY1 */, _1is/* scZI */),
              _1iu/* scZQ */ = function(_1iv/* scZY */, _1iw/* scZZ */, _/* EXTERNAL */){
                while(1){
                  var _1ix/* sd01 */ = E(_1iv/* scZY */);
                  if(!_1ix/* sd01 */._){
                    return _1iw/* scZZ */;
                  }else{
                    var _1iy/* sd04 */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1ix/* sd01 */.a, _1bY/* scD7 */, _1bZ/* scD8 */, _1iw/* scZZ */, _/* EXTERNAL */));
                    _1iv/* scZY */ = _1ix/* sd01 */.b;
                    _1iw/* scZZ */ = _1iy/* sd04 */;
                    continue;
                  }
                }
              },
              _1iz/* sd08 */ = B((function(_1iA/* scZR */, _1iB/* scZS */, _1iC/* scZT */, _/* EXTERNAL */){
                var _1iD/* scZV */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1iA/* scZR */, _1bY/* scD7 */, _1bZ/* scD8 */, _1iC/* scZT */, _/* EXTERNAL */));
                return new F(function(){return _1iu/* scZQ */(_1iB/* scZS */, _1iD/* scZV */, _/* EXTERNAL */);});
              })(_1ip/* scZm */.a, _1ip/* scZm */.b, _1it/* scZM */, _/* EXTERNAL */)),
              _1iE/* sd0d */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
              _1iF/* sd0g */ = __app1/* EXTERNAL */(_1iE/* sd0d */, E(_1iz/* sd08 */));
              return new F(function(){return __app1/* EXTERNAL */(_1iE/* sd0d */, _1iF/* sd0g */);});
            }
          },
          _1iG/* sd0o */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1hV/* scX8 */)).e);
          if(!_1iG/* sd0o */._){
            return new F(function(){return _1in/* scZj */(_/* EXTERNAL */, _1im/* scZ8 */);});
          }else{
            var _1iH/* sd0q */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18b/* FormEngine.FormElement.Rendering.lvl */, _1im/* scZ8 */, _/* EXTERNAL */)),
            _1iI/* sd0v */ = B(_Ib/* FormEngine.JQuery.$wa34 */(_1iG/* sd0o */.a, E(_1iH/* sd0q */), _/* EXTERNAL */));
            return new F(function(){return _1in/* scZj */(_/* EXTERNAL */, E(_1iI/* sd0v */));});
          }
        };
        if(!E(_1hW/* scXa */)._){
          var _1iJ/* sd0D */ = B(_I6/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1ik/* scZ3 */), _/* EXTERNAL */));
          return new F(function(){return _1il/* scZ6 */(_/* EXTERNAL */, E(_1iJ/* sd0D */));});
        }else{
          var _1iK/* sd0M */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1au/* FormEngine.FormElement.Rendering.lvl21 */, E(_1ik/* scZ3 */), _/* EXTERNAL */));
          return new F(function(){return _1il/* scZ6 */(_/* EXTERNAL */, E(_1iK/* sd0M */));});
        }
      };
      if(!E(_1c3/* scDe */.b)){
        return new F(function(){return _1ia/* scYq */(_/* EXTERNAL */, E(_1i9/* scYn */));});
      }else{
        var _1iL/* sd0W */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1aw/* FormEngine.FormElement.Rendering.lvl23 */, _1aw/* FormEngine.FormElement.Rendering.lvl23 */, E(_1i9/* scYn */), _/* EXTERNAL */));
        return new F(function(){return _1ia/* scYq */(_/* EXTERNAL */, E(_1iL/* sd0W */));});
      }
      break;
    case 9:
      return new F(function(){return _19X/* FormEngine.JQuery.errorjq1 */(_1as/* FormEngine.FormElement.Rendering.lvl19 */, _1c0/* scD9 */, _/* EXTERNAL */);});
      break;
    case 10:
      var _1iM/* sd18 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ap/* FormEngine.FormElement.Rendering.lvl16 */, E(_1c0/* scD9 */), _/* EXTERNAL */)),
      _1iN/* sd1d */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
      _1iO/* sd1g */ = __app1/* EXTERNAL */(_1iN/* sd1d */, E(_1iM/* sd18 */)),
      _1iP/* sd1j */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
      _1iQ/* sd1m */ = __app1/* EXTERNAL */(_1iP/* sd1j */, _1iO/* sd1g */),
      _1iR/* sd1p */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18T/* FormEngine.FormElement.Rendering.lvl6 */, _1iQ/* sd1m */, _/* EXTERNAL */)),
      _1iS/* sd1v */ = __app1/* EXTERNAL */(_1iN/* sd1d */, E(_1iR/* sd1p */)),
      _1iT/* sd1z */ = __app1/* EXTERNAL */(_1iP/* sd1j */, _1iS/* sd1v */),
      _1iU/* sd1C */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18U/* FormEngine.FormElement.Rendering.lvl7 */, _1iT/* sd1z */, _/* EXTERNAL */)),
      _1iV/* sd1I */ = __app1/* EXTERNAL */(_1iN/* sd1d */, E(_1iU/* sd1C */)),
      _1iW/* sd1M */ = __app1/* EXTERNAL */(_1iP/* sd1j */, _1iV/* sd1I */),
      _1iX/* sd1P */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ao/* FormEngine.FormElement.Rendering.lvl15 */, _1iW/* sd1M */, _/* EXTERNAL */)),
      _1iY/* sd1V */ = __app1/* EXTERNAL */(_1iN/* sd1d */, E(_1iX/* sd1P */)),
      _1iZ/* sd1Z */ = __app1/* EXTERNAL */(_1iP/* sd1j */, _1iY/* sd1V */),
      _1j0/* sd22 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ar/* FormEngine.FormElement.Rendering.lvl18 */, _1iZ/* sd1Z */, _/* EXTERNAL */)),
      _1j1/* sd2k */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _1j2/* sd2h */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1c3/* scDe */.a)).a);
        if(!_1j2/* sd2h */._){
          return E(_1aq/* FormEngine.FormElement.Rendering.lvl17 */);
        }else{
          return E(_1j2/* sd2h */.a);
        }
      },1), E(_1j0/* sd22 */), _/* EXTERNAL */)),
      _1j3/* sd2p */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
      _1j4/* sd2s */ = __app1/* EXTERNAL */(_1j3/* sd2p */, E(_1j1/* sd2k */)),
      _1j5/* sd2w */ = __app1/* EXTERNAL */(_1j3/* sd2p */, _1j4/* sd2s */),
      _1j6/* sd2A */ = __app1/* EXTERNAL */(_1j3/* sd2p */, _1j5/* sd2w */),
      _1j7/* sd2E */ = __app1/* EXTERNAL */(_1j3/* sd2p */, _1j6/* sd2A */);
      return new F(function(){return _18f/* FormEngine.FormElement.Rendering.a1 */(_1c3/* scDe */, _1j7/* sd2E */, _/* EXTERNAL */);});
      break;
    default:
      var _1j8/* sd2M */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ap/* FormEngine.FormElement.Rendering.lvl16 */, E(_1c0/* scD9 */), _/* EXTERNAL */)),
      _1j9/* sd2R */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
      _1ja/* sd2U */ = __app1/* EXTERNAL */(_1j9/* sd2R */, E(_1j8/* sd2M */)),
      _1jb/* sd2X */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
      _1jc/* sd30 */ = __app1/* EXTERNAL */(_1jb/* sd2X */, _1ja/* sd2U */),
      _1jd/* sd33 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18T/* FormEngine.FormElement.Rendering.lvl6 */, _1jc/* sd30 */, _/* EXTERNAL */)),
      _1je/* sd39 */ = __app1/* EXTERNAL */(_1j9/* sd2R */, E(_1jd/* sd33 */)),
      _1jf/* sd3d */ = __app1/* EXTERNAL */(_1jb/* sd2X */, _1je/* sd39 */),
      _1jg/* sd3g */ = B(_I6/* FormEngine.JQuery.$wa3 */(_18U/* FormEngine.FormElement.Rendering.lvl7 */, _1jf/* sd3d */, _/* EXTERNAL */)),
      _1jh/* sd3m */ = __app1/* EXTERNAL */(_1j9/* sd2R */, E(_1jg/* sd3g */)),
      _1ji/* sd3q */ = __app1/* EXTERNAL */(_1jb/* sd2X */, _1jh/* sd3m */),
      _1jj/* sd3t */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1ao/* FormEngine.FormElement.Rendering.lvl15 */, _1ji/* sd3q */, _/* EXTERNAL */)),
      _1jk/* sd3z */ = __app1/* EXTERNAL */(_1j9/* sd2R */, E(_1jj/* sd3t */)),
      _1jl/* sd3D */ = __app1/* EXTERNAL */(_1jb/* sd2X */, _1jk/* sd3z */),
      _1jm/* sd3G */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1an/* FormEngine.FormElement.Rendering.lvl14 */, _1jl/* sd3D */, _/* EXTERNAL */)),
      _1jn/* sd3Y */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1am/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _1jo/* sd3V */ = E(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1c3/* scDe */.a)).a);
        if(!_1jo/* sd3V */._){
          return E(_1al/* FormEngine.FormElement.Rendering.lvl12 */);
        }else{
          return E(_1jo/* sd3V */.a);
        }
      },1), E(_1jm/* sd3G */), _/* EXTERNAL */)),
      _1jp/* sd43 */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
      _1jq/* sd46 */ = __app1/* EXTERNAL */(_1jp/* sd43 */, E(_1jn/* sd3Y */)),
      _1jr/* sd4a */ = __app1/* EXTERNAL */(_1jp/* sd43 */, _1jq/* sd46 */),
      _1js/* sd4e */ = __app1/* EXTERNAL */(_1jp/* sd43 */, _1jr/* sd4a */),
      _1jt/* sd4i */ = __app1/* EXTERNAL */(_1jp/* sd43 */, _1js/* sd4e */);
      return new F(function(){return _18f/* FormEngine.FormElement.Rendering.a1 */(_1c3/* scDe */, _1jt/* sd4i */, _/* EXTERNAL */);});
  }
},
_1ju/* foldElements1 */ = function(_1jv/* sd4m */, _1jw/* sd4n */, _1jx/* sd4o */, _1jy/* sd4p */, _/* EXTERNAL */){
  var _1jz/* sd4r */ = function(_1jA/* sd4s */, _1jB/* sd4t */, _/* EXTERNAL */){
    while(1){
      var _1jC/* sd4v */ = E(_1jA/* sd4s */);
      if(!_1jC/* sd4v */._){
        return _1jB/* sd4t */;
      }else{
        var _1jD/* sd4y */ = B(_1bW/* FormEngine.FormElement.Rendering.foldElements2 */(_1jC/* sd4v */.a, _1jw/* sd4n */, _1jx/* sd4o */, _1jB/* sd4t */, _/* EXTERNAL */));
        _1jA/* sd4s */ = _1jC/* sd4v */.b;
        _1jB/* sd4t */ = _1jD/* sd4y */;
        continue;
      }
    }
  };
  return new F(function(){return _1jz/* sd4r */(_1jv/* sd4m */, _1jy/* sd4p */, _/* EXTERNAL */);});
},
_1jE/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("textarea"));
}),
_1jF/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("select"));
}),
_1jG/* selectSVG2 */ = "(function (selector, jq) { if (jq[0].contentDocument !== null) { var res = $(selector, jq[0].contentDocument.documentElement); if (res.length === 0) { console.warn(\'empty $ selection \' + selector); }; return res; } else return jq; })",
_1jH/* $wa19 */ = function(_1jI/* snZB */, _1jJ/* snZC */, _/* EXTERNAL */){
  var _1jK/* snZM */ = eval/* EXTERNAL */(E(_1jG/* FormEngine.JQuery.selectSVG2 */));
  return new F(function(){return E(_1jK/* snZM */)(toJSStr/* EXTERNAL */(E(_1jI/* snZB */)), _1jJ/* snZC */);});
},
_1jL/* highlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#FBB48F"));
}),
_1jM/* tinkerDiagSvgConsumer6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("fill"));
}),
_1jN/* tinkerDiagSvgConsumer7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1jO/* tinkerDiagSvgConsumer5 */ = function(_1jP/* shgs */, _1jQ/* shgt */, _/* EXTERNAL */){
  var _1jR/* shgw */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1jN/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1jQ/* shgt */)), _/* EXTERNAL */)),
  _1jS/* shgC */ = B(_1jH/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1jN/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1jP/* shgs */)), E(_1jR/* shgw */), _/* EXTERNAL */)),
  _1jT/* shgH */ = B(_43/* FormEngine.JQuery.$wa2 */(_1jM/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1jL/* DiagramDecorator.highlightCol */, E(_1jS/* shgC */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1jU/* $wa */ = function(_1jV/* shiq */, _/* EXTERNAL */){
  var _1jW/* shiD */ = new T(function(){
    return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1jV/* shiq */));
  }),
  _1jX/* shiE */ = function(_1jY/* shiF */, _/* EXTERNAL */){
    while(1){
      var _1jZ/* shiH */ = E(_1jY/* shiF */);
      if(!_1jZ/* shiH */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1k0/* shiK */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1jZ/* shiH */.a, _1jW/* shiD */, _/* EXTERNAL */));
        _1jY/* shiF */ = _1jZ/* shiH */.b;
        continue;
      }
    }
  },
  _1k1/* shiN */ = B(_1jX/* shiE */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_1jV/* shiq */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1k2/* tinkerDiagramForElement1 */ = function(_1k3/* shiQ */, _1k4/* shiR */, _/* EXTERNAL */){
  return new F(function(){return _1jU/* DiagramDecorator.$wa */(_1k3/* shiQ */, _/* EXTERNAL */);});
},
_1k5/* lvl10 */ = new T1(1,_1k2/* DiagramDecorator.tinkerDiagramForElement1 */),
_1k6/* lowlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("white"));
}),
_1k7/* $wa1 */ = function(_1k8/* shfN */, _/* EXTERNAL */){
  var _1k9/* shg0 */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_1jN/* DiagramDecorator.tinkerDiagSvgConsumer7 */, new T(function(){
      return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1k8/* shfN */));
    },1)));
  }),
  _1ka/* shg2 */ = function(_1kb/* shg3 */, _/* EXTERNAL */){
    while(1){
      var _1kc/* shg5 */ = E(_1kb/* shg3 */);
      if(!_1kc/* shg5 */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1kd/* shg8 */ = B(_50/* FormEngine.JQuery.select1 */(_1k9/* shg0 */, _/* EXTERNAL */)),
        _1ke/* shge */ = B(_1jH/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1jN/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1kc/* shg5 */.a)), E(_1kd/* shg8 */), _/* EXTERNAL */)),
        _1kf/* shgj */ = B(_43/* FormEngine.JQuery.$wa2 */(_1jM/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1k6/* DiagramDecorator.lowlightCol */, E(_1ke/* shge */), _/* EXTERNAL */));
        _1kb/* shg3 */ = _1kc/* shg5 */.b;
        continue;
      }
    }
  },
  _1kg/* shgm */ = B(_1ka/* shg2 */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_1k8/* shfN */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1kh/* tinkerDiagramForElementBlur1 */ = function(_1ki/* shgp */, _1kj/* shgq */, _/* EXTERNAL */){
  return new F(function(){return _1k7/* DiagramDecorator.$wa1 */(_1ki/* shgp */, _/* EXTERNAL */);});
},
_1kk/* lvl11 */ = new T1(1,_1kh/* DiagramDecorator.tinkerDiagramForElementBlur1 */),
_1kl/* lvl12 */ = new T3(0,_1k5/* Form.lvl10 */,_1kk/* Form.lvl11 */,_2o/* GHC.Base.Nothing */),
_1km/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'desc-subpane\'>"));
}),
_1kn/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1ko/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<object class=\'svg-help\' href=\'http://caniuse.com/#feat=svg\' data=\'/static/img/data_process.svg\' type=\'image/svg+xml\'><br>"));
}),
_1kp/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\'long-desc\'>"));
}),
_1kq/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/hint-icon.png\' style=\'margin-right: 5px;\'>"));
}),
_1kr/* baseURL */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/"));
}),
_1ks/* staticURL1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("static/"));
}),
_1kt/* staticURL */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1kr/* Config.Config.baseURL */, _1ks/* Config.Config.staticURL1 */));
}),
_1ku/* lvl18 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1kt/* Config.Config.staticURL */, _1kq/* Form.lvl17 */));
}),
_1kv/* lvl19 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img src=\'", _1ku/* Form.lvl18 */));
}),
_1kw/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'main-pane\'></div>"));
}),
_1kx/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span/>"));
}),
_1ky/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#m_questionnaire_form"));
}),
_1kz/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input"));
}),
_1kA/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input:checked"));
}),
_1kB/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'form-subpane\'>"));
}),
_1kC/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/valid.png\'/>"));
}),
_1kD/* lvl5 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1kt/* Config.Config.staticURL */, _1kC/* Form.lvl4 */));
}),
_1kE/* lvl6 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1kD/* Form.lvl5 */));
}),
_1kF/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/invalid.png\'/>"));
}),
_1kG/* lvl8 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1kt/* Config.Config.staticURL */, _1kF/* Form.lvl7 */));
}),
_1kH/* lvl9 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1kG/* Form.lvl8 */));
}),
_1kI/* click1 */ = function(_1kJ/* snIJ */, _/* EXTERNAL */){
  return new F(function(){return _Lb/* FormEngine.JQuery.$wa5 */(E(_1kJ/* snIJ */), _/* EXTERNAL */);});
},
_1kK/* selectTab1 */ = function(_1kL/* suyF */, _1kM/* suyG */, _/* EXTERNAL */){
  var _1kN/* suyL */ = new T(function(){
    return B(_IH/* FormEngine.FormElement.Identifiers.tabId */(new T(function(){
      return B(_6V/* GHC.List.$w!! */(_1kM/* suyG */, E(_1kL/* suyF */)));
    },1)));
  },1),
  _1kO/* suyN */ = B(_50/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_J3/* FormEngine.FormElement.Tabs.colorizeTabs4 */, _1kN/* suyL */)), _/* EXTERNAL */));
  return new F(function(){return _1kI/* FormEngine.JQuery.click1 */(_1kO/* suyN */, _/* EXTERNAL */);});
},
_1kP/* tinkerDiagSvgConsumer4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_1kQ/* tinkerDiagSvgCurator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_1kR/* tinkerDiagSvgCurator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_1kS/* tinkerDiagSvgCurator5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_1kT/* tinkerDiagSvgCurator6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_1kU/* tinkerDiagSvgCurator8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_1kV/* tinkerDiagSvgInvestigator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution_box"));
}),
_1kW/* tinkerDiagSvgManager4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_1kX/* tinkerDiagramForChapterElement1 */ = function(_1kY/* shiT */, _/* EXTERNAL */){
  var _1kZ/* shj6 */ = B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(B(_4t/* FormEngine.FormElement.FormElement.formItem */(_1kY/* shiT */)))).b));
  if(!_1kZ/* shj6 */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _1l0/* shj8 */ = _1kZ/* shj6 */.b;
    switch(E(_1kZ/* shj6 */.a)){
      case 48:
        if(!E(_1l0/* shj8 */)._){
          var _1l1/* shje */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kV/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 49:
        if(!E(_1l0/* shj8 */)._){
          var _1l2/* shjl */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kW/* DiagramDecorator.tinkerDiagSvgManager4 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 50:
        if(!E(_1l0/* shj8 */)._){
          var _1l3/* shjs */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 51:
        if(!E(_1l0/* shj8 */)._){
          var _1l4/* shjz */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kP/* DiagramDecorator.tinkerDiagSvgConsumer4 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 52:
        if(!E(_1l0/* shj8 */)._){
          var _1l5/* shjG */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 53:
        if(!E(_1l0/* shj8 */)._){
          var _1l6/* shjM */ = new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          }),
          _1l7/* shjN */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kS/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1l6/* shjM */, _/* EXTERNAL */)),
          _1l8/* shjQ */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kR/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1l6/* shjM */, _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 54:
        if(!E(_1l0/* shj8 */)._){
          var _1l9/* shjX */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kQ/* DiagramDecorator.tinkerDiagSvgCurator3 */, new T(function(){
            return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1kY/* shiT */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 55:
        var _1la/* shk2 */ = E(_1l0/* shj8 */);
        return _0/* GHC.Tuple.() */;
      default:
        return _0/* GHC.Tuple.() */;
    }
  }
},
_1lb/* generateQuestionnaire1 */ = function(_1lc/* siiM */, _/* EXTERNAL */){
  var _1ld/* siiO */ = B(_50/* FormEngine.JQuery.select1 */(_1ky/* Form.lvl21 */, _/* EXTERNAL */)),
  _1le/* siiT */ = new T2(1,_Ln/* Form.aboutTab */,_1lc/* siiM */),
  _1lf/* sikL */ = new T(function(){
    var _1lg/* sikK */ = function(_1lh/* siiV */, _/* EXTERNAL */){
      var _1li/* siiX */ = B(_50/* FormEngine.JQuery.select1 */(_1kw/* Form.lvl2 */, _/* EXTERNAL */)),
      _1lj/* sij2 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1kB/* Form.lvl3 */, E(_1li/* siiX */), _/* EXTERNAL */)),
      _1lk/* sij7 */ = E(_HQ/* FormEngine.JQuery.addClassInside_f3 */),
      _1ll/* sija */ = __app1/* EXTERNAL */(_1lk/* sij7 */, E(_1lj/* sij2 */)),
      _1lm/* sijd */ = E(_HP/* FormEngine.JQuery.addClassInside_f2 */),
      _1ln/* sijg */ = __app1/* EXTERNAL */(_1lm/* sijd */, _1ll/* sija */),
      _1lo/* sijl */ = B(_1ju/* FormEngine.FormElement.Rendering.foldElements1 */(B(_HA/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_1lh/* siiV */)), new T3(0,_1lc/* siiM */,_1kE/* Form.lvl6 */,_1kH/* Form.lvl9 */), _1kl/* Form.lvl12 */, _1ln/* sijg */, _/* EXTERNAL */)),
      _1lp/* sijq */ = E(_HO/* FormEngine.JQuery.addClassInside_f1 */),
      _1lq/* sijt */ = __app1/* EXTERNAL */(_1lp/* sijq */, E(_1lo/* sijl */)),
      _1lr/* sijw */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1km/* Form.lvl13 */, _1lq/* sijt */, _/* EXTERNAL */)),
      _1ls/* sijC */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1kn/* Form.lvl14 */, new T(function(){
        return B(_4R/* FormEngine.FormElement.Identifiers.descSubpaneId */(_1lh/* siiV */));
      },1), E(_1lr/* sijw */), _/* EXTERNAL */)),
      _1lt/* sijI */ = __app1/* EXTERNAL */(_1lk/* sij7 */, E(_1ls/* sijC */)),
      _1lu/* sijM */ = __app1/* EXTERNAL */(_1lm/* sijd */, _1lt/* sijI */),
      _1lv/* sijP */ = B(_KQ/* FormEngine.JQuery.$wa26 */(_1ko/* Form.lvl15 */, _1lu/* sijM */, _/* EXTERNAL */)),
      _1lw/* sijV */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1kn/* Form.lvl14 */, new T(function(){
        return B(_Lu/* FormEngine.FormElement.Identifiers.diagramId */(_1lh/* siiV */));
      },1), E(_1lv/* sijP */), _/* EXTERNAL */)),
      _1lx/* sik3 */ = B(_L4/* FormEngine.JQuery.$wa29 */(function(_1ly/* sik0 */, _/* EXTERNAL */){
        return new F(function(){return _1kX/* DiagramDecorator.tinkerDiagramForChapterElement1 */(_1lh/* siiV */, _/* EXTERNAL */);});
      }, E(_1lw/* sijV */), _/* EXTERNAL */)),
      _1lz/* sik8 */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1kp/* Form.lvl16 */, E(_1lx/* sik3 */), _/* EXTERNAL */)),
      _1lA/* sike */ = B(_HR/* FormEngine.JQuery.$wa20 */(_1kn/* Form.lvl14 */, new T(function(){
        return B(_Lr/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_1lh/* siiV */));
      },1), E(_1lz/* sik8 */), _/* EXTERNAL */)),
      _1lB/* sikk */ = __app1/* EXTERNAL */(_1lk/* sij7 */, E(_1lA/* sike */)),
      _1lC/* siko */ = __app1/* EXTERNAL */(_1lm/* sijd */, _1lB/* sikk */),
      _1lD/* sikr */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1kv/* Form.lvl19 */, _1lC/* siko */, _/* EXTERNAL */)),
      _1lE/* sikw */ = B(_I6/* FormEngine.JQuery.$wa3 */(_1kx/* Form.lvl20 */, E(_1lD/* sikr */), _/* EXTERNAL */)),
      _1lF/* sikC */ = __app1/* EXTERNAL */(_1lp/* sijq */, E(_1lE/* sikw */));
      return new F(function(){return __app1/* EXTERNAL */(_1lp/* sijq */, _1lF/* sikC */);});
    };
    return B(_2S/* GHC.Base.map */(_1lg/* sikK */, _1lc/* siiM */));
  }),
  _1lG/* sikN */ = B(_JC/* FormEngine.FormElement.Tabs.$wa */(_1le/* siiT */, new T2(1,_Lp/* Form.aboutTabPaneJq1 */,_1lf/* sikL */), E(_1ld/* siiO */), _/* EXTERNAL */)),
  _1lH/* sikQ */ = B(_1kK/* FormEngine.FormElement.Tabs.selectTab1 */(_Lf/* Form.aboutTab4 */, _1le/* siiT */, _/* EXTERNAL */)),
  _1lI/* sikT */ = B(_50/* FormEngine.JQuery.select1 */(_1kA/* Form.lvl23 */, _/* EXTERNAL */)),
  _1lJ/* sikY */ = B(_Lb/* FormEngine.JQuery.$wa5 */(E(_1lI/* sikT */), _/* EXTERNAL */)),
  _1lK/* sil3 */ = B(_Lb/* FormEngine.JQuery.$wa5 */(E(_1lJ/* sikY */), _/* EXTERNAL */)),
  _1lL/* sil6 */ = B(_50/* FormEngine.JQuery.select1 */(_1kz/* Form.lvl22 */, _/* EXTERNAL */)),
  _1lM/* silb */ = B(_KL/* FormEngine.JQuery.$wa14 */(E(_1lL/* sil6 */), _/* EXTERNAL */)),
  _1lN/* sile */ = B(_50/* FormEngine.JQuery.select1 */(_1jE/* Form.lvl */, _/* EXTERNAL */)),
  _1lO/* silj */ = B(_KL/* FormEngine.JQuery.$wa14 */(E(_1lN/* sile */), _/* EXTERNAL */)),
  _1lP/* silm */ = B(_50/* FormEngine.JQuery.select1 */(_1jF/* Form.lvl1 */, _/* EXTERNAL */)),
  _1lQ/* silr */ = B(_KL/* FormEngine.JQuery.$wa14 */(E(_1lP/* silm */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1lR/* go */ = function(_1lS/* sNEu */){
  while(1){
    var _1lT/* sNEv */ = E(_1lS/* sNEu */);
    if(!_1lT/* sNEv */._){
      return false;
    }else{
      if(!E(_1lT/* sNEv */.a)._){
        return true;
      }else{
        _1lS/* sNEu */ = _1lT/* sNEv */.b;
        continue;
      }
    }
  }
},
_1lU/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Generate"));
}),
_1lV/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Error generating tabs"));
}),
_1lW/* a2 */ = function(_1lX/* s1vnB */, _1lY/* s1vnC */){
  return new F(function(){return _1lZ/* GHC.Read.$wa20 */(_1lY/* s1vnC */);});
},
_1lZ/* $wa20 */ = function(_1m0/* s1vnD */){
  var _1m1/* s1vnI */ = new T(function(){
    return B(_119/* Text.Read.Lex.expect2 */(function(_1m2/* s1vnF */){
      var _1m3/* s1vnG */ = E(_1m2/* s1vnF */);
      if(!_1m3/* s1vnG */._){
        return new F(function(){return A1(_1m0/* s1vnD */,_1m3/* s1vnG */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1m4/* s1vnJ */ = function(_1m5/* s1vnK */){
    return E(_1m1/* s1vnI */);
  };
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1m6/* s1vnL */){
    return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1m6/* s1vnL */, _1m4/* s1vnJ */);});
  }), new T(function(){
    return new T1(1,B(_11H/* GHC.Read.$wa3 */(_1lW/* GHC.Read.a2 */, _1m0/* s1vnD */)));
  }));});
},
_1m7/* $fReadChar2 */ = function(_1m8/* s1vnR */, _1m9/* s1vnS */){
  return new F(function(){return _1lZ/* GHC.Read.$wa20 */(_1m9/* s1vnS */);});
},
_1ma/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("["));
}),
_1mb/* $wa */ = function(_1mc/* s1vjF */, _1md/* s1vjG */){
  var _1me/* s1vjH */ = function(_1mf/* s1vjI */, _1mg/* s1vjJ */){
    var _1mh/* s1vjK */ = new T(function(){
      return B(A1(_1mg/* s1vjJ */,_I/* GHC.Types.[] */));
    }),
    _1mi/* s1vjL */ = new T(function(){
      var _1mj/* s1vjQ */ = function(_1mk/* s1vjM */){
        return new F(function(){return _1me/* s1vjH */(_8g/* GHC.Types.True */, function(_1ml/* s1vjN */){
          return new F(function(){return A1(_1mg/* s1vjJ */,new T2(1,_1mk/* s1vjM */,_1ml/* s1vjN */));});
        });});
      };
      return B(A2(_1mc/* s1vjF */,_11G/* Text.ParserCombinators.ReadPrec.minPrec */, _1mj/* s1vjQ */));
    }),
    _1mm/* s1vk8 */ = new T(function(){
      return B(_119/* Text.Read.Lex.expect2 */(function(_1mn/* s1vjS */){
        var _1mo/* s1vjT */ = E(_1mn/* s1vjS */);
        if(_1mo/* s1vjT */._==2){
          var _1mp/* s1vjV */ = E(_1mo/* s1vjT */.a);
          if(!_1mp/* s1vjV */._){
            return new T0(2);
          }else{
            var _1mq/* s1vjX */ = _1mp/* s1vjV */.b;
            switch(E(_1mp/* s1vjV */.a)){
              case 44:
                return (E(_1mq/* s1vjX */)._==0) ? (!E(_1mf/* s1vjI */)) ? new T0(2) : E(_1mi/* s1vjL */) : new T0(2);
              case 93:
                return (E(_1mq/* s1vjX */)._==0) ? E(_1mh/* s1vjK */) : new T0(2);
              default:
                return new T0(2);
            }
          }
        }else{
          return new T0(2);
        }
      }));
    }),
    _1mr/* s1vk9 */ = function(_1ms/* s1vka */){
      return E(_1mm/* s1vk8 */);
    };
    return new T1(1,function(_1mt/* s1vkb */){
      return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1mt/* s1vkb */, _1mr/* s1vk9 */);});
    });
  },
  _1mu/* s1vkd */ = function(_1mv/* s1vkf */, _1mw/* s1vkg */){
    return new F(function(){return _1mx/* s1vke */(_1mw/* s1vkg */);});
  },
  _1mx/* s1vke */ = function(_1my/* s1vkh */){
    var _1mz/* s1vki */ = new T(function(){
      var _1mA/* s1vkj */ = new T(function(){
        var _1mB/* s1vkq */ = new T(function(){
          var _1mC/* s1vkp */ = function(_1mD/* s1vkl */){
            return new F(function(){return _1me/* s1vjH */(_8g/* GHC.Types.True */, function(_1mE/* s1vkm */){
              return new F(function(){return A1(_1my/* s1vkh */,new T2(1,_1mD/* s1vkl */,_1mE/* s1vkm */));});
            });});
          };
          return B(A2(_1mc/* s1vjF */,_11G/* Text.ParserCombinators.ReadPrec.minPrec */, _1mC/* s1vkp */));
        });
        return B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_1me/* s1vjH */(_2G/* GHC.Types.False */, _1my/* s1vkh */)), _1mB/* s1vkq */));
      });
      return B(_119/* Text.Read.Lex.expect2 */(function(_1mF/* s1vkr */){
        var _1mG/* s1vks */ = E(_1mF/* s1vkr */);
        return (_1mG/* s1vks */._==2) ? (!B(_IO/* GHC.Base.eqString */(_1mG/* s1vks */.a, _1ma/* GHC.Read.lvl6 */))) ? new T0(2) : E(_1mA/* s1vkj */) : new T0(2);
      }));
    }),
    _1mH/* s1vkw */ = function(_1mI/* s1vkx */){
      return E(_1mz/* s1vki */);
    };
    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1mJ/* s1vky */){
      return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1mJ/* s1vky */, _1mH/* s1vkw */);});
    }), new T(function(){
      return new T1(1,B(_11H/* GHC.Read.$wa3 */(_1mu/* s1vkd */, _1my/* s1vkh */)));
    }));});
  };
  return new F(function(){return _1mx/* s1vke */(_1md/* s1vjG */);});
},
_1mK/* a7 */ = function(_1mL/* s1vpn */, _1mM/* s1vpo */){
  return new F(function(){return _1mN/* GHC.Read.$wa19 */(_1mM/* s1vpo */);});
},
_1mN/* $wa19 */ = function(_1mO/* s1vpp */){
  var _1mP/* s1vpu */ = new T(function(){
    return B(_119/* Text.Read.Lex.expect2 */(function(_1mQ/* s1vpr */){
      var _1mR/* s1vps */ = E(_1mQ/* s1vpr */);
      if(_1mR/* s1vps */._==1){
        return new F(function(){return A1(_1mO/* s1vpp */,_1mR/* s1vps */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1mS/* s1vpv */ = function(_1mT/* s1vpw */){
    return E(_1mP/* s1vpu */);
  };
  return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1mU/* s1vpx */){
    return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1mU/* s1vpx */, _1mS/* s1vpv */);});
  }), new T(function(){
    return B(_1mb/* GHC.Read.$wa */(_1m7/* GHC.Read.$fReadChar2 */, _1mO/* s1vpp */));
  }))), new T(function(){
    return new T1(1,B(_11H/* GHC.Read.$wa3 */(_1mK/* GHC.Read.a7 */, _1mO/* s1vpp */)));
  }));});
},
_1mV/* $fReadChar1 */ = function(_1mW/* s1vpF */, _1mX/* s1vpG */){
  return new F(function(){return _1mN/* GHC.Read.$wa19 */(_1mX/* s1vpG */);});
},
_1mY/* $fRead[]3 */ = function(_1mZ/* s1vpI */, _1n0/* s1vpJ */){
  return new F(function(){return _1mb/* GHC.Read.$wa */(_1mV/* GHC.Read.$fReadChar1 */, _1n0/* s1vpJ */);});
},
_1n1/* $fRead[]5 */ = new T(function(){
  return B(_1mb/* GHC.Read.$wa */(_1mV/* GHC.Read.$fReadChar1 */, _QP/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1n2/* $fRead[]4 */ = function(_1n3/* B1 */){
  return new F(function(){return _Oz/* Text.ParserCombinators.ReadP.run */(_1n1/* GHC.Read.$fRead[]5 */, _1n3/* B1 */);});
},
_1n4/* $fReadChar4 */ = new T(function(){
  return B(_1mN/* GHC.Read.$wa19 */(_QP/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1n5/* $fReadChar3 */ = function(_1n3/* B1 */){
  return new F(function(){return _Oz/* Text.ParserCombinators.ReadP.run */(_1n4/* GHC.Read.$fReadChar4 */, _1n3/* B1 */);});
},
_1n6/* $fRead[]_$s$creadsPrec1 */ = function(_1n7/* s1vpH */, _1n3/* B1 */){
  return new F(function(){return _1n5/* GHC.Read.$fReadChar3 */(_1n3/* B1 */);});
},
_1n8/* $fRead[]_$s$fRead[]1 */ = new T4(0,_1n6/* GHC.Read.$fRead[]_$s$creadsPrec1 */,_1n2/* GHC.Read.$fRead[]4 */,_1mV/* GHC.Read.$fReadChar1 */,_1mY/* GHC.Read.$fRead[]3 */),
_1n9/* $fRead(,)6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_1na/* readPrec */ = function(_1nb/* s1vgA */){
  return E(E(_1nb/* s1vgA */).c);
},
_1nc/* $fRead(,)5 */ = function(_1nd/* s1vtd */, _1ne/* s1vte */, _1nf/* s1vtf */){
  var _1ng/* s1vtg */ = new T(function(){
    return B(_1na/* GHC.Read.readPrec */(_1ne/* s1vte */));
  }),
  _1nh/* s1vth */ = new T(function(){
    return B(A2(_1na/* GHC.Read.readPrec */,_1nd/* s1vtd */, _1nf/* s1vtf */));
  }),
  _1ni/* s1vtz */ = function(_1nj/* s1vti */){
    var _1nk/* s1vty */ = function(_1nl/* s1vtj */){
      var _1nm/* s1vtk */ = new T(function(){
        var _1nn/* s1vtl */ = new T(function(){
          return B(A2(_1ng/* s1vtg */,_1nf/* s1vtf */, function(_1no/* s1vtm */){
            return new F(function(){return A1(_1nj/* s1vti */,new T2(0,_1nl/* s1vtj */,_1no/* s1vtm */));});
          }));
        });
        return B(_119/* Text.Read.Lex.expect2 */(function(_1np/* s1vtp */){
          var _1nq/* s1vtq */ = E(_1np/* s1vtp */);
          return (_1nq/* s1vtq */._==2) ? (!B(_IO/* GHC.Base.eqString */(_1nq/* s1vtq */.a, _1n9/* GHC.Read.$fRead(,)6 */))) ? new T0(2) : E(_1nn/* s1vtl */) : new T0(2);
        }));
      }),
      _1nr/* s1vtu */ = function(_1ns/* s1vtv */){
        return E(_1nm/* s1vtk */);
      };
      return new T1(1,function(_1nt/* s1vtw */){
        return new F(function(){return A2(_ZQ/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1nt/* s1vtw */, _1nr/* s1vtu */);});
      });
    };
    return new F(function(){return A1(_1nh/* s1vth */,_1nk/* s1vty */);});
  };
  return E(_1ni/* s1vtz */);
},
_1nu/* $wa2 */ = function(_1nv/* s1vuR */, _1nw/* s1vuS */, _1nx/* s1vuT */){
  var _1ny/* s1vuU */ = function(_1n3/* B1 */){
    return new F(function(){return _1nc/* GHC.Read.$fRead(,)5 */(_1nv/* s1vuR */, _1nw/* s1vuS */, _1n3/* B1 */);});
  },
  _1nz/* s1vuV */ = function(_1nA/* s1vuX */, _1nB/* s1vuY */){
    return new F(function(){return _1nC/* s1vuW */(_1nB/* s1vuY */);});
  },
  _1nC/* s1vuW */ = function(_1nD/* s1vuZ */){
    return new F(function(){return _PJ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_11H/* GHC.Read.$wa3 */(_1ny/* s1vuU */, _1nD/* s1vuZ */))), new T(function(){
      return new T1(1,B(_11H/* GHC.Read.$wa3 */(_1nz/* s1vuV */, _1nD/* s1vuZ */)));
    }));});
  };
  return new F(function(){return _1nC/* s1vuW */(_1nx/* s1vuT */);});
},
_1nE/* $s$fRead(,)3 */ = function(_1nF/* sNBH */, _1nG/* sNBI */){
  return new F(function(){return _1nu/* GHC.Read.$wa2 */(_1n8/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1n8/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1nG/* sNBI */);});
},
_1nH/* lvl6 */ = new T(function(){
  return B(_1mb/* GHC.Read.$wa */(_1nE/* Main.$s$fRead(,)3 */, _12L/* Text.Read.readEither5 */));
}),
_1nI/* lookup */ = function(_1nJ/* s9uF */, _1nK/* s9uG */, _1nL/* s9uH */){
  while(1){
    var _1nM/* s9uI */ = E(_1nL/* s9uH */);
    if(!_1nM/* s9uI */._){
      return __Z/* EXTERNAL */;
    }else{
      var _1nN/* s9uL */ = E(_1nM/* s9uI */.a);
      if(!B(A3(_Uc/* GHC.Classes.== */,_1nJ/* s9uF */, _1nK/* s9uG */, _1nN/* s9uL */.a))){
        _1nL/* s9uH */ = _1nM/* s9uI */.b;
        continue;
      }else{
        return new T1(1,_1nN/* s9uL */.b);
      }
    }
  }
},
_1nO/* getMaybeNumberFIUnitValue */ = function(_1nP/* scjQ */, _1nQ/* scjR */){
  var _1nR/* scjS */ = E(_1nQ/* scjR */);
  if(!_1nR/* scjS */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1nS/* scjU */ = E(_1nP/* scjQ */);
    if(_1nS/* scjU */._==3){
      var _1nT/* scjY */ = E(_1nS/* scjU */.b);
      switch(_1nT/* scjY */._){
        case 0:
          return new T1(1,_1nT/* scjY */.a);
        case 1:
          return new F(function(){return _1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_12/* GHC.Base.++ */(B(_4M/* FormEngine.FormItem.numbering2text */(E(_1nS/* scjU */.a).b)), _Or/* FormEngine.FormItem.nfiUnitId1 */));
          }), _1nR/* scjS */.a);});
          break;
        default:
          return __Z/* EXTERNAL */;
      }
    }else{
      return E(_16D/* FormEngine.FormItem.nfiUnit1 */);
    }
  }
},
_1nU/* fiId */ = function(_1nV/* s7yC */){
  return new F(function(){return _4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1nV/* s7yC */)).b);});
},
_1nW/* isCheckboxChecked1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("on"));
}),
_1nX/* isCheckboxChecked */ = function(_1nY/* scjJ */, _1nZ/* scjK */){
  var _1o0/* scjL */ = E(_1nZ/* scjK */);
  if(!_1o0/* scjL */._){
    return false;
  }else{
    var _1o1/* scjO */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_1nU/* FormEngine.FormItem.fiId */(_1nY/* scjJ */));
    }), _1o0/* scjL */.a));
    if(!_1o1/* scjO */._){
      return false;
    }else{
      return new F(function(){return _IO/* GHC.Base.eqString */(_1o1/* scjO */.a, _1nW/* FormEngine.FormData.isCheckboxChecked1 */);});
    }
  }
},
_1o2/* isOptionSelected */ = function(_1o3/* scjh */, _1o4/* scji */, _1o5/* scjj */){
  var _1o6/* scjk */ = E(_1o5/* scjj */);
  if(!_1o6/* scjk */._){
    return false;
  }else{
    var _1o7/* scjx */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_4M/* FormEngine.FormItem.numbering2text */(B(_4q/* FormEngine.FormItem.fiDescriptor */(_1o4/* scji */)).b));
    }), _1o6/* scjk */.a));
    if(!_1o7/* scjx */._){
      return false;
    }else{
      var _1o8/* scjy */ = _1o7/* scjx */.a,
      _1o9/* scjz */ = E(_1o3/* scjh */);
      if(!_1o9/* scjz */._){
        return new F(function(){return _IO/* GHC.Base.eqString */(_1o8/* scjy */, _1o9/* scjz */.a);});
      }else{
        return new F(function(){return _IO/* GHC.Base.eqString */(_1o8/* scjy */, _1o9/* scjz */.b);});
      }
    }
  }
},
_1oa/* maybeStr2maybeInt2 */ = new T(function(){
  return B(A3(_12b/* GHC.Read.$fReadInt3 */,_12E/* GHC.Read.$fReadInt_$sconvertInt */, _11G/* Text.ParserCombinators.ReadPrec.minPrec */, _QP/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1ob/* maybeStr2maybeInt1 */ = function(_1oc/* s637 */){
  var _1od/* s638 */ = B(_Oz/* Text.ParserCombinators.ReadP.run */(_1oa/* FormEngine.FormElement.FormElement.maybeStr2maybeInt2 */, _1oc/* s637 */));
  return (_1od/* s638 */._==0) ? __Z/* EXTERNAL */ : (E(_1od/* s638 */.b)._==0) ? new T1(1,E(_1od/* s638 */.a).a) : __Z/* EXTERNAL */;
},
_1oe/* makeElem */ = function(_1of/* s63k */, _1og/* s63l */, _1oh/* s63m */){
  var _1oi/* s63n */ = E(_1oh/* s63m */);
  switch(_1oi/* s63n */._){
    case 0:
      var _1oj/* s63E */ = new T(function(){
        var _1ok/* s63p */ = E(_1og/* s63l */);
        if(!_1ok/* s63p */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1ol/* s63C */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4M/* FormEngine.FormItem.numbering2text */(E(_1oi/* s63n */.a).b));
          }), _1ok/* s63p */.a));
          if(!_1ol/* s63C */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1ol/* s63C */.a);
          }
        }
      });
      return new T1(1,new T3(1,_1oi/* s63n */,_1oj/* s63E */,_1of/* s63k */));
    case 1:
      var _1om/* s63W */ = new T(function(){
        var _1on/* s63H */ = E(_1og/* s63l */);
        if(!_1on/* s63H */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1oo/* s63U */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4M/* FormEngine.FormItem.numbering2text */(E(_1oi/* s63n */.a).b));
          }), _1on/* s63H */.a));
          if(!_1oo/* s63U */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1oo/* s63U */.a);
          }
        }
      });
      return new T1(1,new T3(2,_1oi/* s63n */,_1om/* s63W */,_1of/* s63k */));
    case 2:
      var _1op/* s64e */ = new T(function(){
        var _1oq/* s63Z */ = E(_1og/* s63l */);
        if(!_1oq/* s63Z */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1or/* s64c */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4M/* FormEngine.FormItem.numbering2text */(E(_1oi/* s63n */.a).b));
          }), _1oq/* s63Z */.a));
          if(!_1or/* s64c */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1or/* s64c */.a);
          }
        }
      });
      return new T1(1,new T3(3,_1oi/* s63n */,_1op/* s64e */,_1of/* s63k */));
    case 3:
      var _1os/* s64x */ = new T(function(){
        var _1ot/* s64i */ = E(_1og/* s63l */);
        if(!_1ot/* s64i */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1ou/* s64v */ = B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4M/* FormEngine.FormItem.numbering2text */(E(_1oi/* s63n */.a).b));
          }), _1ot/* s64i */.a));
          if(!_1ou/* s64v */._){
            return __Z/* EXTERNAL */;
          }else{
            return B(_1ob/* FormEngine.FormElement.FormElement.maybeStr2maybeInt1 */(_1ou/* s64v */.a));
          }
        }
      });
      return new T1(1,new T4(4,_1oi/* s63n */,_1os/* s64x */,new T(function(){
        return B(_1nO/* FormEngine.FormData.getMaybeNumberFIUnitValue */(_1oi/* s63n */, _1og/* s63l */));
      }),_1of/* s63k */));
    case 4:
      var _1ov/* s64C */ = new T(function(){
        return new T3(5,_1oi/* s63n */,_1ow/* s64D */,_1of/* s63k */);
      }),
      _1ow/* s64D */ = new T(function(){
        var _1ox/* s64P */ = function(_1oy/* s64E */){
          var _1oz/* s64F */ = E(_1oy/* s64E */);
          if(!_1oz/* s64F */._){
            return new T2(0,_1oz/* s64F */,new T(function(){
              return B(_1o2/* FormEngine.FormData.isOptionSelected */(_1oz/* s64F */, _1oi/* s63n */, _1og/* s63l */));
            }));
          }else{
            var _1oA/* s64O */ = new T(function(){
              return B(_5C/* Data.Maybe.catMaybes1 */(B(_2S/* GHC.Base.map */(function(_1oB/* B1 */){
                return new F(function(){return _1oe/* FormEngine.FormElement.FormElement.makeElem */(_1ov/* s64C */, _1og/* s63l */, _1oB/* B1 */);});
              }, _1oz/* s64F */.c))));
            });
            return new T3(1,_1oz/* s64F */,new T(function(){
              return B(_1o2/* FormEngine.FormData.isOptionSelected */(_1oz/* s64F */, _1oi/* s63n */, _1og/* s63l */));
            }),_1oA/* s64O */);
          }
        };
        return B(_2S/* GHC.Base.map */(_1ox/* s64P */, _1oi/* s63n */.b));
      });
      return new T1(1,_1ov/* s64C */);
    case 5:
      var _1oC/* s655 */ = new T(function(){
        var _1oD/* s64S */ = E(_1og/* s63l */);
        if(!_1oD/* s64S */._){
          return __Z/* EXTERNAL */;
        }else{
          return B(_1nI/* GHC.List.lookup */(_QC/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4M/* FormEngine.FormItem.numbering2text */(E(_1oi/* s63n */.a).b));
          }), _1oD/* s64S */.a));
        }
      });
      return new T1(1,new T3(6,_1oi/* s63n */,_1oC/* s655 */,_1of/* s63k */));
    case 6:
      return __Z/* EXTERNAL */;
    case 7:
      var _1oE/* s65c */ = new T(function(){
        return new T3(7,_1oi/* s63n */,_1oF/* s65d */,_1of/* s63k */);
      }),
      _1oF/* s65d */ = new T(function(){
        return B(_5C/* Data.Maybe.catMaybes1 */(B(_2S/* GHC.Base.map */(function(_1oB/* B1 */){
          return new F(function(){return _1oe/* FormEngine.FormElement.FormElement.makeElem */(_1oE/* s65c */, _1og/* s63l */, _1oB/* B1 */);});
        }, _1oi/* s63n */.c))));
      });
      return new T1(1,_1oE/* s65c */);
    case 8:
      var _1oG/* s65k */ = new T(function(){
        return new T4(8,_1oi/* s63n */,new T(function(){
          return B(_1nX/* FormEngine.FormData.isCheckboxChecked */(_1oi/* s63n */, _1og/* s63l */));
        }),_1oH/* s65l */,_1of/* s63k */);
      }),
      _1oH/* s65l */ = new T(function(){
        return B(_5C/* Data.Maybe.catMaybes1 */(B(_2S/* GHC.Base.map */(function(_1oB/* B1 */){
          return new F(function(){return _1oe/* FormEngine.FormElement.FormElement.makeElem */(_1oG/* s65k */, _1og/* s63l */, _1oB/* B1 */);});
        }, _1oi/* s63n */.c))));
      });
      return new T1(1,_1oG/* s65k */);
    case 9:
      var _1oI/* s65r */ = new T(function(){
        return new T3(9,_1oi/* s63n */,_1oJ/* s65s */,_1of/* s63k */);
      }),
      _1oJ/* s65s */ = new T(function(){
        return B(_5C/* Data.Maybe.catMaybes1 */(B(_2S/* GHC.Base.map */(function(_1oB/* B1 */){
          return new F(function(){return _1oe/* FormEngine.FormElement.FormElement.makeElem */(_1oI/* s65r */, _1og/* s63l */, _1oB/* B1 */);});
        }, _1oi/* s63n */.c))));
      });
      return new T1(1,_1oI/* s65r */);
    case 10:
      return new T1(1,new T2(10,_1oi/* s63n */,_1of/* s63k */));
    default:
      return new T1(1,new T2(11,_1oi/* s63n */,_1of/* s63k */));
  }
},
_1oK/* onResize2 */ = "(function (ev, jq) { jq.resize(ev); })",
_1oL/* onResize1 */ = function(_1oM/* snCd */, _1oN/* snCe */, _/* EXTERNAL */){
  var _1oO/* snCq */ = __createJSFunc/* EXTERNAL */(2, function(_1oP/* snCh */, _/* EXTERNAL */){
    var _1oQ/* snCj */ = B(A2(E(_1oM/* snCd */),_1oP/* snCh */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1oR/* snCt */ = E(_1oN/* snCe */),
  _1oS/* snCy */ = eval/* EXTERNAL */(E(_1oK/* FormEngine.JQuery.onResize2 */)),
  _1oT/* snCG */ = E(_1oS/* snCy */)(_1oO/* snCq */, _1oR/* snCt */);
  return _1oR/* snCt */;
},
_1oU/* onScroll2 */ = "(function (ev, jq) { jq.scroll(ev); })",
_1oV/* onScroll1 */ = function(_1oW/* snCM */, _1oX/* snCN */, _/* EXTERNAL */){
  var _1oY/* snCZ */ = __createJSFunc/* EXTERNAL */(2, function(_1oZ/* snCQ */, _/* EXTERNAL */){
    var _1p0/* snCS */ = B(A2(E(_1oW/* snCM */),_1oZ/* snCQ */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1p1/* snD2 */ = E(_1oX/* snCN */),
  _1p2/* snD7 */ = eval/* EXTERNAL */(E(_1oU/* FormEngine.JQuery.onScroll2 */)),
  _1p3/* snDf */ = E(_1p2/* snD7 */)(_1oY/* snCZ */, _1p1/* snD2 */);
  return _1p1/* snD2 */;
},
_1p4/* pageTabGroup17 */ = 600,
_1p5/* pageTabGroup16 */ = new T2(1,_1p4/* Page.pageTabGroup17 */,_I/* GHC.Types.[] */),
_1p6/* pageTabGroup15 */ = new T2(1,_1p5/* Page.pageTabGroup16 */,_2H/* Page.pageTabGroup10 */),
_1p7/* pageTabGroup14 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1p6/* Page.pageTabGroup15 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1p8/* pageTabGroup13 */ = new T2(6,_1p7/* Page.pageTabGroup14 */,_I/* GHC.Types.[] */),
_1p9/* mQuestionnaireTab */ = new T3(0,_1p8/* Page.pageTabGroup13 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1pa/* pageTabGroup12 */ = 700,
_1pb/* pageTabGroup11 */ = new T2(1,_1pa/* Page.pageTabGroup12 */,_I/* GHC.Types.[] */),
_1pc/* pageTabGroup9 */ = new T2(1,_1pb/* Page.pageTabGroup11 */,_2H/* Page.pageTabGroup10 */),
_1pd/* pageTabGroup8 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1pc/* Page.pageTabGroup9 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1pe/* pageTabGroup7 */ = new T2(6,_1pd/* Page.pageTabGroup8 */,_I/* GHC.Types.[] */),
_1pf/* tQuestionnaireTab */ = new T3(0,_1pe/* Page.pageTabGroup7 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1pg/* pageTabGroup6 */ = new T2(1,_1pf/* Page.tQuestionnaireTab */,_I/* GHC.Types.[] */),
_1ph/* pageTabGroup5 */ = new T2(1,_1p9/* Page.mQuestionnaireTab */,_1pg/* Page.pageTabGroup6 */),
_1pi/* pageTabGroup22 */ = 500,
_1pj/* pageTabGroup21 */ = new T2(1,_1pi/* Page.pageTabGroup22 */,_I/* GHC.Types.[] */),
_1pk/* pageTabGroup20 */ = new T2(1,_1pj/* Page.pageTabGroup21 */,_2H/* Page.pageTabGroup10 */),
_1pl/* pageTabGroup19 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1pk/* Page.pageTabGroup20 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1pm/* pageTabGroup18 */ = new T2(6,_1pl/* Page.pageTabGroup19 */,_I/* GHC.Types.[] */),
_1pn/* rolesTab */ = new T3(0,_1pm/* Page.pageTabGroup18 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1po/* pageTabGroup4 */ = new T2(1,_1pn/* Page.rolesTab */,_1ph/* Page.pageTabGroup5 */),
_1pp/* pageTabGroup3 */ = new T2(1,_3R/* Page.dataTab */,_1po/* Page.pageTabGroup4 */),
_1pq/* pageTabGroup2 */ = new T2(1,_3Z/* Page.lifecycleTab */,_1pp/* Page.pageTabGroup3 */),
_1pr/* pageTabGroup1 */ = new T2(1,_2N/* Page.actionTab */,_1pq/* Page.pageTabGroup2 */),
_1ps/* pageTabGroup42 */ = 100,
_1pt/* pageTabGroup41 */ = new T2(1,_1ps/* Page.pageTabGroup42 */,_I/* GHC.Types.[] */),
_1pu/* pageTabGroup40 */ = new T2(1,_1pt/* Page.pageTabGroup41 */,_2H/* Page.pageTabGroup10 */),
_1pv/* pageTabGroup39 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1pu/* Page.pageTabGroup40 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1pw/* pageTabGroup38 */ = new T2(6,_1pv/* Page.pageTabGroup39 */,_I/* GHC.Types.[] */),
_1px/* visionTab */ = new T3(0,_1pw/* Page.pageTabGroup38 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1py/* pageTabGroup */ = new T2(1,_1px/* Page.visionTab */,_1pr/* Page.pageTabGroup1 */),
_1pz/* getWidth_f1 */ = new T(function(){
  return (function (jq) { return jq.width(); });
}),
_1pA/* resizeHandler2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".svg-help"));
}),
_1pB/* resizeHandler_paneSel */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".desc-subpane"));
}),
_1pC/* setWidth_f1 */ = new T(function(){
  return (function (val, jq) { jq.width(val); return jq; });
}),
_1pD/* $wa */ = function(_/* EXTERNAL */){
  var _1pE/* sNBN */ = E(_4V/* FormEngine.JQuery.getWindow_f1 */)(),
  _1pF/* sNBT */ = E(_1pz/* FormEngine.JQuery.getWidth_f1 */)(_1pE/* sNBN */),
  _1pG/* sNBW */ = B(_50/* FormEngine.JQuery.select1 */(_1pB/* Main.resizeHandler_paneSel */, _/* EXTERNAL */)),
  _1pH/* sNC0 */ = Number/* EXTERNAL */(_1pF/* sNBT */),
  _1pI/* sNC4 */ = jsTrunc/* EXTERNAL */(_1pH/* sNC0 */),
  _1pJ/* sNCf */ = E(_1pC/* FormEngine.JQuery.setWidth_f1 */),
  _1pK/* sNCi */ = _1pJ/* sNCf */(_1pI/* sNC4 */-790|0, E(_1pG/* sNBW */)),
  _1pL/* sNCl */ = B(_50/* FormEngine.JQuery.select1 */(_1pA/* Main.resizeHandler2 */, _/* EXTERNAL */)),
  _1pM/* sNCr */ = _1pJ/* sNCf */(_1pI/* sNC4 */-795|0, E(_1pL/* sNCl */));
  return _0/* GHC.Tuple.() */;
},
_1pN/* resizeHandler1 */ = function(_1pO/* sNCu */, _/* EXTERNAL */){
  return new F(function(){return _1pD/* Main.$wa */(_/* EXTERNAL */);});
},
_1pP/* time2 */ = "(function (label) { console.time(label); })",
_1pQ/* time1 */ = function(_1pR/* snAa */, _/* EXTERNAL */){
  var _1pS/* snAk */ = eval/* EXTERNAL */(E(_1pP/* FormEngine.JQuery.time2 */)),
  _1pT/* snAs */ = E(_1pS/* snAk */)(toJSStr/* EXTERNAL */(E(_1pR/* snAa */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1pU/* timeEnd2 */ = "(function (label) { console.timeEnd(label); })",
_1pV/* timeEnd1 */ = function(_1pW/* snzM */, _/* EXTERNAL */){
  var _1pX/* snzW */ = eval/* EXTERNAL */(E(_1pU/* FormEngine.JQuery.timeEnd2 */)),
  _1pY/* snA4 */ = E(_1pX/* snzW */)(toJSStr/* EXTERNAL */(E(_1pW/* snzM */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1pZ/* lvl15 */ = function(_1q0/* sNEA */, _/* EXTERNAL */){
  var _1q1/* sNED */ = new T(function(){
    var _1q2/* sNEI */ = B(_Os/* Text.Read.readEither6 */(B(_Oz/* Text.ParserCombinators.ReadP.run */(_1nH/* Main.lvl6 */, new T(function(){
      var _1q3/* sNEE */ = E(_1q0/* sNEA */);
      if(!_1q3/* sNEE */._){
        return __Z/* EXTERNAL */;
      }else{
        return E(_1q3/* sNEE */.a);
      }
    })))));
    if(!_1q2/* sNEI */._){
      return __Z/* EXTERNAL */;
    }else{
      if(!E(_1q2/* sNEI */.b)._){
        return new T1(1,_1q2/* sNEI */.a);
      }else{
        return __Z/* EXTERNAL */;
      }
    }
  }),
  _1q4/* sNEW */ = function(_1q5/* sNEO */){
    var _1q6/* sNEP */ = E(_1q5/* sNEO */);
    if(_1q6/* sNEP */._==6){
      var _1q7/* sNES */ = new T(function(){
        return new T3(0,_1q6/* sNEP */,_1q8/* sNET */,_2G/* GHC.Types.False */);
      }),
      _1q8/* sNET */ = new T(function(){
        return B(_5C/* Data.Maybe.catMaybes1 */(B(_2S/* GHC.Base.map */(function(_1q9/* B1 */){
          return new F(function(){return _1oe/* FormEngine.FormElement.FormElement.makeElem */(_1q7/* sNES */, _1q1/* sNED */, _1q9/* B1 */);});
        }, _1q6/* sNEP */.b))));
      });
      return new T1(1,_1q7/* sNES */);
    }else{
      return __Z/* EXTERNAL */;
    }
  },
  _1qa/* sNEC */ = B(_2S/* GHC.Base.map */(_1q4/* sNEW */, _Hq/* FormStructure.FormStructure.formItems */));
  if(!B(_1lR/* Main.go */(_1qa/* sNEC */))){
    var _1qb/* sNEY */ = B(_1pQ/* FormEngine.JQuery.time1 */(_1lU/* Main.lvl11 */, _/* EXTERNAL */)),
    _1qc/* sNF1 */ = new T(function(){
      return B(_5C/* Data.Maybe.catMaybes1 */(_1qa/* sNEC */));
    }),
    _1qd/* sNF2 */ = B(_1lb/* Form.generateQuestionnaire1 */(_1qc/* sNF1 */, _/* EXTERNAL */)),
    _1qe/* sNF5 */ = B(_1pV/* FormEngine.JQuery.timeEnd1 */(_1lU/* Main.lvl11 */, _/* EXTERNAL */)),
    _1qf/* sNF8 */ = E(_4V/* FormEngine.JQuery.getWindow_f1 */),
    _1qg/* sNFb */ = _1qf/* sNF8 */(),
    _1qh/* sNFi */ = B(_1oV/* FormEngine.JQuery.onScroll1 */(function(_1qi/* sNFe */, _/* EXTERNAL */){
      return new F(function(){return _53/* Main.$wa1 */(_1qc/* sNF1 */, _/* EXTERNAL */);});
    }, _1qg/* sNFb */, _/* EXTERNAL */)),
    _1qj/* sNFm */ = _1qf/* sNF8 */(),
    _1qk/* sNFq */ = B(_1oL/* FormEngine.JQuery.onResize1 */(_1pN/* Main.resizeHandler1 */, _1qj/* sNFm */, _/* EXTERNAL */)),
    _1ql/* sNFu */ = _1qf/* sNF8 */(),
    _1qm/* sNFx */ = B(_5y/* FormEngine.JQuery.$wa17 */(_1ql/* sNFu */, _/* EXTERNAL */)),
    _1qn/* sNFA */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_1px/* Page.visionTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }else{
    var _1qo/* sNFD */ = B(_5K/* FormEngine.JQuery.errorIO1 */(_1lV/* Main.lvl14 */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_1qp/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_investigator"));
}),
_1qq/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_manager"));
}),
_1qr/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_steward"));
}),
_1qs/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_custodian"));
}),
_1qt/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_curator"));
}),
_1qu/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_consumer"));
}),
_1qv/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_expert"));
}),
_1qw/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_producer"));
}),
_1qx/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_public"));
}),
_1qy/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_secondary"));
}),
_1qz/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_primary"));
}),
_1qA/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_raw"));
}),
_1qB/* overlay2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_1qC/* overlay3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("body"));
}),
_1qD/* overlay4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("div"));
}),
_1qE/* $w$j */ = function(_/* EXTERNAL */, _1qF/* sJNt */){
  var _1qG/* sJNu */ = B(_18B/* FormEngine.JQuery.$wa9 */(_1qD/* Overlay.overlay4 */, _1qF/* sJNt */, _/* EXTERNAL */)),
  _1qH/* sJNx */ = B(_50/* FormEngine.JQuery.select1 */(_1qC/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1qI/* sJNF */ = E(_4T/* FormEngine.JQuery.getScrollTop_f1 */)(E(_1qH/* sJNx */)),
  _1qJ/* sJNJ */ = Number/* EXTERNAL */(_1qI/* sJNF */),
  _1qK/* sJNN */ = jsTrunc/* EXTERNAL */(_1qJ/* sJNJ */);
  return new F(function(){return _43/* FormEngine.JQuery.$wa2 */(_1qB/* Overlay.overlay2 */, B(_4e/* GHC.Show.$wshowSignedInt */(0, _1qK/* sJNN */+25|0, _I/* GHC.Types.[] */)), E(_1qG/* sJNu */), _/* EXTERNAL */);});
},
_1qL/* getCss2 */ = "(function (key, jq) { return jq.css(key); })",
_1qM/* $wa11 */ = function(_1qN/* snSA */, _1qO/* snSB */, _/* EXTERNAL */){
  var _1qP/* snSL */ = eval/* EXTERNAL */(E(_1qL/* FormEngine.JQuery.getCss2 */)),
  _1qQ/* snST */ = E(_1qP/* snSL */)(toJSStr/* EXTERNAL */(E(_1qN/* snSA */)), _1qO/* snSB */);
  return new T(function(){
    return String/* EXTERNAL */(_1qQ/* snST */);
  });
},
_1qR/* getHeight_f1 */ = new T(function(){
  return (function (jq) { return jq.height(); });
}),
_1qS/* hideJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hidden"));
}),
_1qT/* hideJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1qU/* overlay5 */ = "visible",
_1qV/* overlay6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1qW/* setHeight_f1 */ = new T(function(){
  return (function (val, jq) { jq.height(val); return jq; });
}),
_1qX/* showJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visible"));
}),
_1qY/* overlay1 */ = function(_1qZ/* sJNU */, _/* EXTERNAL */){
  var _1r0/* sJNX */ = B(_50/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", _1qZ/* sJNU */)), _/* EXTERNAL */)),
  _1r1/* sJO0 */ = B(_50/* FormEngine.JQuery.select1 */(_1qC/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1r2/* sJO8 */ = E(_1qR/* FormEngine.JQuery.getHeight_f1 */)(E(_1r1/* sJO0 */)),
  _1r3/* sJOc */ = Number/* EXTERNAL */(_1r2/* sJO8 */),
  _1r4/* sJOg */ = jsTrunc/* EXTERNAL */(_1r3/* sJOc */),
  _1r5/* sJOq */ = E(_1qW/* FormEngine.JQuery.setHeight_f1 */)(_1r4/* sJOg */, E(_1r0/* sJNX */)),
  _1r6/* sJOt */ = B(_1qM/* FormEngine.JQuery.$wa11 */(_1qV/* Overlay.overlay6 */, _1r5/* sJOq */, _/* EXTERNAL */)),
  _1r7/* sJOB */ = strEq/* EXTERNAL */(E(_1r6/* sJOt */), E(_1qU/* Overlay.overlay5 */));
  if(!E(_1r7/* sJOB */)){
    var _1r8/* sJOK */ = B(_43/* FormEngine.JQuery.$wa2 */(_1qT/* FormEngine.JQuery.hideJq3 */, _1qX/* FormEngine.JQuery.showJq2 */, _1r5/* sJOq */, _/* EXTERNAL */));
    return new F(function(){return _1qE/* Overlay.$w$j */(_/* EXTERNAL */, E(_1r8/* sJOK */));});
  }else{
    var _1r9/* sJOF */ = B(_43/* FormEngine.JQuery.$wa2 */(_1qT/* FormEngine.JQuery.hideJq3 */, _1qS/* FormEngine.JQuery.hideJq2 */, _1r5/* sJOq */, _/* EXTERNAL */));
    return new F(function(){return _1qE/* Overlay.$w$j */(_/* EXTERNAL */, E(_1r9/* sJOF */));});
  }
},
_1ra/* ready_f1 */ = new T(function(){
  return (function (f) { jQuery(document).ready(f); });
}),
_1rb/* tinkerDiagSvgConsumer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_consumer"));
}),
_1rc/* tinkerDiagSvgConsumer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kP/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1rb/* DiagramDecorator.tinkerDiagSvgConsumer3 */, _/* EXTERNAL */);});
},
_1rd/* tinkerDiagSvgConsumer1 */ = function(_1re/* shgN */, _/* EXTERNAL */){
  return new F(function(){return _1rc/* DiagramDecorator.tinkerDiagSvgConsumer2 */(_/* EXTERNAL */);});
},
_1rf/* tinkerDiagSvgCurator7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_curator"));
}),
_1rg/* tinkerDiagSvgCurator2 */ = function(_/* EXTERNAL */){
  var _1rh/* shhr */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1ri/* shhu */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kP/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1rj/* shhx */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1rk/* shhA */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kS/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1rl/* shhD */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kR/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kQ/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1rf/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */);});
},
_1rm/* tinkerDiagSvgCurator1 */ = function(_1rn/* shhG */, _/* EXTERNAL */){
  return new F(function(){return _1rg/* DiagramDecorator.tinkerDiagSvgCurator2 */(_/* EXTERNAL */);});
},
_1ro/* tinkerDiagSvgCustodian3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_custodian"));
}),
_1rp/* tinkerDiagSvgCustodian2 */ = function(_/* EXTERNAL */){
  var _1rq/* shhI */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1ro/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */)),
  _1rr/* shhL */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kS/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1ro/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kR/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1ro/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */);});
},
_1rs/* tinkerDiagSvgCustodian1 */ = function(_1rt/* shhO */, _/* EXTERNAL */){
  return new F(function(){return _1rp/* DiagramDecorator.tinkerDiagSvgCustodian2 */(_/* EXTERNAL */);});
},
_1ru/* tinkerDiagSvgExpert3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_expert"));
}),
_1rv/* tinkerDiagSvgExpert2 */ = function(_/* EXTERNAL */){
  var _1rw/* shhm */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1ru/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1ru/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */);});
},
_1rx/* tinkerDiagSvgExpert1 */ = function(_1ry/* shhp */, _/* EXTERNAL */){
  return new F(function(){return _1rv/* DiagramDecorator.tinkerDiagSvgExpert2 */(_/* EXTERNAL */);});
},
_1rz/* tinkerDiagSvgInvestigator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_investigator"));
}),
_1rA/* tinkerDiagSvgInvestigator2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kV/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, _1rz/* DiagramDecorator.tinkerDiagSvgInvestigator3 */, _/* EXTERNAL */);});
},
_1rB/* tinkerDiagSvgInvestigator1 */ = function(_1rC/* shgM */, _/* EXTERNAL */){
  return new F(function(){return _1rA/* DiagramDecorator.tinkerDiagSvgInvestigator2 */(_/* EXTERNAL */);});
},
_1rD/* tinkerDiagSvgManager3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_manager"));
}),
_1rE/* tinkerDiagSvgManager2 */ = function(_/* EXTERNAL */){
  var _1rF/* shia */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kW/* DiagramDecorator.tinkerDiagSvgManager4 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1rG/* shid */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1rH/* shig */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1rI/* shij */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kS/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1rJ/* shim */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kR/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kQ/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1rD/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */);});
},
_1rK/* tinkerDiagSvgManager1 */ = function(_1rL/* ship */, _/* EXTERNAL */){
  return new F(function(){return _1rE/* DiagramDecorator.tinkerDiagSvgManager2 */(_/* EXTERNAL */);});
},
_1rM/* tinkerDiagSvgPrimary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_1rN/* tinkerDiagSvgPrimary4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_1rO/* tinkerDiagSvgPrimary5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_secondary"));
}),
_1rP/* tinkerDiagSvgPrimary6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_2"));
}),
_1rQ/* tinkerDiagSvgPrimary7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_primary"));
}),
_1rR/* tinkerDiagSvgPrimary2 */ = function(_/* EXTERNAL */){
  var _1rS/* shh0 */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1rQ/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */)),
  _1rT/* shh3 */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1rP/* DiagramDecorator.tinkerDiagSvgPrimary6 */, _1rO/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1rU/* shh6 */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1rN/* DiagramDecorator.tinkerDiagSvgPrimary4 */, _1rQ/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1rM/* DiagramDecorator.tinkerDiagSvgPrimary3 */, _1rQ/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */);});
},
_1rV/* tinkerDiagSvgPrimary1 */ = function(_1rW/* shh9 */, _/* EXTERNAL */){
  return new F(function(){return _1rR/* DiagramDecorator.tinkerDiagSvgPrimary2 */(_/* EXTERNAL */);});
},
_1rX/* tinkerDiagSvgProducer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_producer"));
}),
_1rY/* tinkerDiagSvgProducer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kW/* DiagramDecorator.tinkerDiagSvgManager4 */, _1rX/* DiagramDecorator.tinkerDiagSvgProducer3 */, _/* EXTERNAL */);});
},
_1rZ/* tinkerDiagSvgProducer1 */ = function(_1s0/* shgL */, _/* EXTERNAL */){
  return new F(function(){return _1rY/* DiagramDecorator.tinkerDiagSvgProducer2 */(_/* EXTERNAL */);});
},
_1s1/* tinkerDiagSvgPublic3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_public"));
}),
_1s2/* tinkerDiagSvgPublic4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_H_3"));
}),
_1s3/* tinkerDiagSvgPublic2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1s2/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1s1/* DiagramDecorator.tinkerDiagSvgPublic3 */, _/* EXTERNAL */);});
},
_1s4/* tinkerDiagSvgPublic1 */ = function(_1s5/* shgK */, _/* EXTERNAL */){
  return new F(function(){return _1s3/* DiagramDecorator.tinkerDiagSvgPublic2 */(_/* EXTERNAL */);});
},
_1s6/* tinkerDiagSvgRaw3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_3"));
}),
_1s7/* tinkerDiagSvgRaw4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_1s8/* tinkerDiagSvgRaw5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_1s9/* tinkerDiagSvgRaw6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_raw"));
}),
_1sa/* tinkerDiagSvgRaw2 */ = function(_/* EXTERNAL */){
  var _1sb/* shgP */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kW/* DiagramDecorator.tinkerDiagSvgManager4 */, _1s9/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1sc/* shgS */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1s8/* DiagramDecorator.tinkerDiagSvgRaw5 */, _1s9/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1sd/* shgV */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1s7/* DiagramDecorator.tinkerDiagSvgRaw4 */, _1s9/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1s6/* DiagramDecorator.tinkerDiagSvgRaw3 */, _1s9/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */);});
},
_1se/* tinkerDiagSvgRaw1 */ = function(_1sf/* shgY */, _/* EXTERNAL */){
  return new F(function(){return _1sa/* DiagramDecorator.tinkerDiagSvgRaw2 */(_/* EXTERNAL */);});
},
_1sg/* tinkerDiagSvgSecondary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_1sh/* tinkerDiagSvgSecondary2 */ = function(_/* EXTERNAL */){
  var _1si/* shhb */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kP/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1rO/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1sj/* shhe */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1rO/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1sk/* shhh */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1s2/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1rO/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sg/* DiagramDecorator.tinkerDiagSvgSecondary3 */, _1rO/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */);});
},
_1sl/* tinkerDiagSvgSecondary1 */ = function(_1sm/* shhk */, _/* EXTERNAL */){
  return new F(function(){return _1sh/* DiagramDecorator.tinkerDiagSvgSecondary2 */(_/* EXTERNAL */);});
},
_1sn/* tinkerDiagSvgSteward3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_steward"));
}),
_1so/* tinkerDiagSvgSteward2 */ = function(_/* EXTERNAL */){
  var _1sp/* shhQ */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kW/* DiagramDecorator.tinkerDiagSvgManager4 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1sq/* shhT */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kU/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1sr/* shhW */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kP/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1ss/* shhZ */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kT/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1st/* shi2 */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kS/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1su/* shi5 */ = B(_1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kR/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */));
  return new F(function(){return _1jO/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kQ/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1sn/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */);});
},
_1sv/* tinkerDiagSvgSteward1 */ = function(_1sw/* shi8 */, _/* EXTERNAL */){
  return new F(function(){return _1so/* DiagramDecorator.tinkerDiagSvgSteward2 */(_/* EXTERNAL */);});
},
_1sx/* main1 */ = function(_/* EXTERNAL */){
  var _1sy/* sNLi */ = function(_/* EXTERNAL */){
    var _1sz/* sNG2 */ = function(_1sA/* sNFN */, _/* EXTERNAL */){
      return new F(function(){return _1qY/* Overlay.overlay1 */(new T(function(){
        var _1sB/* sNFS */ = String/* EXTERNAL */(E(_1sA/* sNFN */));
        return fromJSStr/* EXTERNAL */(_1sB/* sNFS */);
      }), _/* EXTERNAL */);});
    },
    _1sC/* sNG6 */ = __createJSFunc/* EXTERNAL */(2, E(_1sz/* sNG2 */)),
    _1sD/* sNGb */ = "(function(s,f){Haste[s] = f;})",
    _1sE/* sNGf */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1sF/* sNGn */ = E(_1sE/* sNGf */)("overlay", _1sC/* sNG6 */),
    _1sG/* sNGE */ = __createJSFunc/* EXTERNAL */(2, function(_1sH/* sNGv */, _/* EXTERNAL */){
      var _1sI/* sNGx */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_1px/* Page.visionTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1sJ/* sNGI */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1sK/* sNGQ */ = E(_1sJ/* sNGI */)("toVision", _1sG/* sNGE */),
    _1sL/* sNH7 */ = __createJSFunc/* EXTERNAL */(2, function(_1sM/* sNGY */, _/* EXTERNAL */){
      var _1sN/* sNH0 */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_2N/* Page.actionTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1sO/* sNHb */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1sP/* sNHj */ = E(_1sO/* sNHb */)("toAction", _1sL/* sNH7 */),
    _1sQ/* sNHA */ = __createJSFunc/* EXTERNAL */(2, function(_1sR/* sNHr */, _/* EXTERNAL */){
      var _1sS/* sNHt */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_3Z/* Page.lifecycleTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1sT/* sNHE */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1sU/* sNHM */ = E(_1sT/* sNHE */)("toLifecycle", _1sQ/* sNHA */),
    _1sV/* sNI3 */ = __createJSFunc/* EXTERNAL */(2, function(_1sW/* sNHU */, _/* EXTERNAL */){
      var _1sX/* sNHW */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_3R/* Page.dataTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1sY/* sNI7 */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1sZ/* sNIf */ = E(_1sY/* sNI7 */)("toData", _1sV/* sNI3 */),
    _1t0/* sNIw */ = __createJSFunc/* EXTERNAL */(2, function(_1t1/* sNIn */, _/* EXTERNAL */){
      var _1t2/* sNIp */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_1pn/* Page.rolesTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1t3/* sNIA */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1t4/* sNII */ = E(_1t3/* sNIA */)("toRoles", _1t0/* sNIw */),
    _1t5/* sNIZ */ = __createJSFunc/* EXTERNAL */(2, function(_1t6/* sNIQ */, _/* EXTERNAL */){
      var _1t7/* sNIS */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_1p9/* Page.mQuestionnaireTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1t8/* sNJ3 */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1t9/* sNJb */ = E(_1t8/* sNJ3 */)("toMQuestionnaire", _1t5/* sNIZ */),
    _1ta/* sNJs */ = __createJSFunc/* EXTERNAL */(2, function(_1tb/* sNJj */, _/* EXTERNAL */){
      var _1tc/* sNJl */ = B(_Ju/* FormEngine.FormElement.Tabs.toTab1 */(_1pf/* Page.tQuestionnaireTab */, _1py/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1td/* sNJw */ = eval/* EXTERNAL */(_1sD/* sNGb */),
    _1te/* sNJE */ = E(_1td/* sNJw */)("toTQuestionnaire", _1ta/* sNJs */),
    _1tf/* sNJH */ = B(_50/* FormEngine.JQuery.select1 */(_1qA/* Main.lvl27 */, _/* EXTERNAL */)),
    _1tg/* sNJK */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1se/* DiagramDecorator.tinkerDiagSvgRaw1 */, _1tf/* sNJH */, _/* EXTERNAL */)),
    _1th/* sNJN */ = B(_50/* FormEngine.JQuery.select1 */(_1qz/* Main.lvl26 */, _/* EXTERNAL */)),
    _1ti/* sNJQ */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rV/* DiagramDecorator.tinkerDiagSvgPrimary1 */, _1th/* sNJN */, _/* EXTERNAL */)),
    _1tj/* sNJT */ = B(_50/* FormEngine.JQuery.select1 */(_1qy/* Main.lvl25 */, _/* EXTERNAL */)),
    _1tk/* sNJW */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1sl/* DiagramDecorator.tinkerDiagSvgSecondary1 */, _1tj/* sNJT */, _/* EXTERNAL */)),
    _1tl/* sNJZ */ = B(_50/* FormEngine.JQuery.select1 */(_1qx/* Main.lvl24 */, _/* EXTERNAL */)),
    _1tm/* sNK2 */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1s4/* DiagramDecorator.tinkerDiagSvgPublic1 */, _1tl/* sNJZ */, _/* EXTERNAL */)),
    _1tn/* sNK5 */ = B(_50/* FormEngine.JQuery.select1 */(_1qw/* Main.lvl23 */, _/* EXTERNAL */)),
    _1to/* sNK8 */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rZ/* DiagramDecorator.tinkerDiagSvgProducer1 */, _1tn/* sNK5 */, _/* EXTERNAL */)),
    _1tp/* sNKb */ = B(_50/* FormEngine.JQuery.select1 */(_1qv/* Main.lvl22 */, _/* EXTERNAL */)),
    _1tq/* sNKe */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rx/* DiagramDecorator.tinkerDiagSvgExpert1 */, _1tp/* sNKb */, _/* EXTERNAL */)),
    _1tr/* sNKh */ = B(_50/* FormEngine.JQuery.select1 */(_1qu/* Main.lvl21 */, _/* EXTERNAL */)),
    _1ts/* sNKk */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rd/* DiagramDecorator.tinkerDiagSvgConsumer1 */, _1tr/* sNKh */, _/* EXTERNAL */)),
    _1tt/* sNKn */ = B(_50/* FormEngine.JQuery.select1 */(_1qt/* Main.lvl20 */, _/* EXTERNAL */)),
    _1tu/* sNKq */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rm/* DiagramDecorator.tinkerDiagSvgCurator1 */, _1tt/* sNKn */, _/* EXTERNAL */)),
    _1tv/* sNKt */ = B(_50/* FormEngine.JQuery.select1 */(_1qs/* Main.lvl19 */, _/* EXTERNAL */)),
    _1tw/* sNKw */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rs/* DiagramDecorator.tinkerDiagSvgCustodian1 */, _1tv/* sNKt */, _/* EXTERNAL */)),
    _1tx/* sNKz */ = B(_50/* FormEngine.JQuery.select1 */(_1qr/* Main.lvl18 */, _/* EXTERNAL */)),
    _1ty/* sNKC */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1sv/* DiagramDecorator.tinkerDiagSvgSteward1 */, _1tx/* sNKz */, _/* EXTERNAL */)),
    _1tz/* sNKF */ = B(_50/* FormEngine.JQuery.select1 */(_1qq/* Main.lvl17 */, _/* EXTERNAL */)),
    _1tA/* sNKI */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rK/* DiagramDecorator.tinkerDiagSvgManager1 */, _1tz/* sNKF */, _/* EXTERNAL */)),
    _1tB/* sNKL */ = B(_50/* FormEngine.JQuery.select1 */(_1qp/* Main.lvl16 */, _/* EXTERNAL */)),
    _1tC/* sNKO */ = B(_KV/* FormEngine.JQuery.onLoad1 */(_1rB/* DiagramDecorator.tinkerDiagSvgInvestigator1 */, _1tB/* sNKL */, _/* EXTERNAL */)),
    _1tD/* sNKR */ = B(_50/* FormEngine.JQuery.select1 */(_3T/* Main.getRespondentKey2 */, _/* EXTERNAL */)),
    _1tE/* sNKZ */ = E(_3S/* FormEngine.JQuery.getRadioValue_f1 */)(E(_1tD/* sNKR */)),
    _1tF/* sNLf */ = B(A(_3j/* Haste.Ajax.ajaxRequest */,[_2E/* Control.Monad.IO.Class.$fMonadIOIO */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _d/* Haste.Prim.JSType.$fJSType[] */, _2F/* Haste.Ajax.POST */, _40/* Main.lvl12 */, new T2(1,new T2(0,_41/* Main.lvl13 */,new T(function(){
      var _1tG/* sNL3 */ = String/* EXTERNAL */(_1tE/* sNKZ */);
      return toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_1tG/* sNL3 */));
    })),_I/* GHC.Types.[] */), _1pZ/* Main.lvl15 */, _/* EXTERNAL */]));
    return _3e/* Haste.Prim.Any.jsNull */;
  },
  _1tH/* sNLm */ = __createJSFunc/* EXTERNAL */(0, E(_1sy/* sNLi */)),
  _1tI/* sNLs */ = E(_1ra/* FormEngine.JQuery.ready_f1 */)(_1tH/* sNLm */);
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1tJ/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1sx/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1tJ, [0]));};window.onload = hasteMain;