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
  return (function (jq) { return jq.val(); });
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
_42/* $fShowMaybe1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just "));
}),
_43/* $fShowMaybe3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nothing"));
}),
_44/* itos */ = function(_45/* sfbi */, _46/* sfbj */){
  var _47/* sfbl */ = jsShowI/* EXTERNAL */(_45/* sfbi */);
  return new F(function(){return _12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_47/* sfbl */), _46/* sfbj */);});
},
_48/* shows7 */ = 41,
_49/* shows8 */ = 40,
_4a/* $wshowSignedInt */ = function(_4b/* sfbq */, _4c/* sfbr */, _4d/* sfbs */){
  if(_4c/* sfbr */>=0){
    return new F(function(){return _44/* GHC.Show.itos */(_4c/* sfbr */, _4d/* sfbs */);});
  }else{
    if(_4b/* sfbq */<=6){
      return new F(function(){return _44/* GHC.Show.itos */(_4c/* sfbr */, _4d/* sfbs */);});
    }else{
      return new T2(1,_49/* GHC.Show.shows8 */,new T(function(){
        var _4e/* sfby */ = jsShowI/* EXTERNAL */(_4c/* sfbr */);
        return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_4e/* sfby */), new T2(1,_48/* GHC.Show.shows7 */,_4d/* sfbs */)));
      }));
    }
  }
},
_4f/* fiDescriptor */ = function(_4g/* s5u2 */){
  var _4h/* s5u3 */ = E(_4g/* s5u2 */);
  switch(_4h/* s5u3 */._){
    case 0:
      return E(_4h/* s5u3 */.a);
    case 1:
      return E(_4h/* s5u3 */.a);
    case 2:
      return E(_4h/* s5u3 */.a);
    case 3:
      return E(_4h/* s5u3 */.a);
    case 4:
      return E(_4h/* s5u3 */.a);
    case 5:
      return E(_4h/* s5u3 */.a);
    case 6:
      return E(_4h/* s5u3 */.a);
    case 7:
      return E(_4h/* s5u3 */.a);
    case 8:
      return E(_4h/* s5u3 */.a);
    case 9:
      return E(_4h/* s5u3 */.a);
    case 10:
      return E(_4h/* s5u3 */.a);
    case 11:
      return E(_4h/* s5u3 */.a);
    default:
      return E(_4h/* s5u3 */.a);
  }
},
_4i/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SubmitButtonElem id="));
}),
_4j/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SaveButtonElem id="));
}),
_4k/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" unit="));
}),
_4l/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NumberElem id="));
}),
_4m/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EmailElem id="));
}),
_4n/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TextElem id="));
}),
_4o/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("StringElem id="));
}),
_4p/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChapterElem id="));
}),
_4q/* shows5 */ = 34,
_4r/* lvl16 */ = new T2(1,_4q/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_4s/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElem id="));
}),
_4t/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" children: "));
}),
_4u/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OptionalGroupElem id="));
}),
_4v/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SimpleGroupElem id="));
}),
_4w/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" value="));
}),
_4x/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ListElem id="));
}),
_4y/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ChoiceElem id="));
}),
_4z/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("InfoElem id="));
}),
_4A/* $fShowInt_$cshow */ = function(_4B/* sffD */){
  return new F(function(){return _4a/* GHC.Show.$wshowSignedInt */(0, E(_4B/* sffD */), _I/* GHC.Types.[] */);});
},
_4C/* $wgo */ = function(_4D/* s5va */, _4E/* s5vb */){
  var _4F/* s5vc */ = E(_4D/* s5va */);
  if(!_4F/* s5vc */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4G/* s5vd */ = _4F/* s5vc */.a,
    _4H/* s5vf */ = E(_4E/* s5vb */);
    return (_4H/* s5vf */==1) ? new T2(1,new T(function(){
      return B(_4A/* GHC.Show.$fShowInt_$cshow */(_4G/* s5vd */));
    }),_I/* GHC.Types.[] */) : new T2(1,new T(function(){
      return B(_4A/* GHC.Show.$fShowInt_$cshow */(_4G/* s5vd */));
    }),new T(function(){
      return B(_4C/* FormEngine.FormItem.$wgo */(_4F/* s5vc */.b, _4H/* s5vf */-1|0));
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
_4Q/* numbering2text */ = function(_4R/* s5vk */){
  var _4S/* s5vl */ = E(_4R/* s5vk */);
  if(!_4S/* s5vl */._){
    return __Z/* EXTERNAL */;
  }else{
    var _4T/* s5vq */ = E(_4S/* s5vl */.b)+1|0;
    if(0>=_4T/* s5vq */){
      return __Z/* EXTERNAL */;
    }else{
      var _4U/* s5vt */ = B(_4C/* FormEngine.FormItem.$wgo */(_4S/* s5vl */.a, _4T/* s5vq */));
      if(!_4U/* s5vt */._){
        return __Z/* EXTERNAL */;
      }else{
        return new F(function(){return _4I/* Data.OldList.intercalate1 */(new T2(1,_4U/* s5vt */.a,new T(function(){
          return B(_4M/* Data.OldList.prependToAll */(_4L/* FormEngine.FormItem.numbering2text1 */, _4U/* s5vt */.b));
        })));});
      }
    }
  }
},
_4V/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: negative index"));
}),
_4W/* prel_list_str */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Prelude."));
}),
_4X/* lvl2 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_4W/* GHC.List.prel_list_str */, _4V/* GHC.List.lvl1 */));
}),
_4Y/* negIndex */ = new T(function(){
  return B(err/* EXTERNAL */(_4X/* GHC.List.lvl2 */));
}),
_4Z/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!!: index too large"));
}),
_50/* lvl4 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_4W/* GHC.List.prel_list_str */, _4Z/* GHC.List.lvl3 */));
}),
_51/* !!1 */ = new T(function(){
  return B(err/* EXTERNAL */(_50/* GHC.List.lvl4 */));
}),
_52/* poly_$wgo2 */ = function(_53/* s9uh */, _54/* s9ui */){
  while(1){
    var _55/* s9uj */ = E(_53/* s9uh */);
    if(!_55/* s9uj */._){
      return E(_51/* GHC.List.!!1 */);
    }else{
      var _56/* s9um */ = E(_54/* s9ui */);
      if(!_56/* s9um */){
        return E(_55/* s9uj */.a);
      }else{
        _53/* s9uh */ = _55/* s9uj */.b;
        _54/* s9ui */ = _56/* s9um */-1|0;
        continue;
      }
    }
  }
},
_57/* $w!! */ = function(_58/* s9uo */, _59/* s9up */){
  if(_59/* s9up */>=0){
    return new F(function(){return _52/* GHC.List.poly_$wgo2 */(_58/* s9uo */, _59/* s9up */);});
  }else{
    return E(_4Y/* GHC.List.negIndex */);
  }
},
_5a/* asciiTab59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_5b/* asciiTab58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_5c/* asciiTab57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_5d/* asciiTab33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_5e/* asciiTab32 */ = new T2(1,_5d/* GHC.Show.asciiTab33 */,_I/* GHC.Types.[] */),
_5f/* asciiTab34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_5g/* asciiTab31 */ = new T2(1,_5f/* GHC.Show.asciiTab34 */,_5e/* GHC.Show.asciiTab32 */),
_5h/* asciiTab35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_5i/* asciiTab30 */ = new T2(1,_5h/* GHC.Show.asciiTab35 */,_5g/* GHC.Show.asciiTab31 */),
_5j/* asciiTab36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_5k/* asciiTab29 */ = new T2(1,_5j/* GHC.Show.asciiTab36 */,_5i/* GHC.Show.asciiTab30 */),
_5l/* asciiTab37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_5m/* asciiTab28 */ = new T2(1,_5l/* GHC.Show.asciiTab37 */,_5k/* GHC.Show.asciiTab29 */),
_5n/* asciiTab38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_5o/* asciiTab27 */ = new T2(1,_5n/* GHC.Show.asciiTab38 */,_5m/* GHC.Show.asciiTab28 */),
_5p/* asciiTab39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_5q/* asciiTab26 */ = new T2(1,_5p/* GHC.Show.asciiTab39 */,_5o/* GHC.Show.asciiTab27 */),
_5r/* asciiTab40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_5s/* asciiTab25 */ = new T2(1,_5r/* GHC.Show.asciiTab40 */,_5q/* GHC.Show.asciiTab26 */),
_5t/* asciiTab41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_5u/* asciiTab24 */ = new T2(1,_5t/* GHC.Show.asciiTab41 */,_5s/* GHC.Show.asciiTab25 */),
_5v/* asciiTab42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_5w/* asciiTab23 */ = new T2(1,_5v/* GHC.Show.asciiTab42 */,_5u/* GHC.Show.asciiTab24 */),
_5x/* asciiTab43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_5y/* asciiTab22 */ = new T2(1,_5x/* GHC.Show.asciiTab43 */,_5w/* GHC.Show.asciiTab23 */),
_5z/* asciiTab44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_5A/* asciiTab21 */ = new T2(1,_5z/* GHC.Show.asciiTab44 */,_5y/* GHC.Show.asciiTab22 */),
_5B/* asciiTab45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_5C/* asciiTab20 */ = new T2(1,_5B/* GHC.Show.asciiTab45 */,_5A/* GHC.Show.asciiTab21 */),
_5D/* asciiTab46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_5E/* asciiTab19 */ = new T2(1,_5D/* GHC.Show.asciiTab46 */,_5C/* GHC.Show.asciiTab20 */),
_5F/* asciiTab47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_5G/* asciiTab18 */ = new T2(1,_5F/* GHC.Show.asciiTab47 */,_5E/* GHC.Show.asciiTab19 */),
_5H/* asciiTab48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_5I/* asciiTab17 */ = new T2(1,_5H/* GHC.Show.asciiTab48 */,_5G/* GHC.Show.asciiTab18 */),
_5J/* asciiTab49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_5K/* asciiTab16 */ = new T2(1,_5J/* GHC.Show.asciiTab49 */,_5I/* GHC.Show.asciiTab17 */),
_5L/* asciiTab50 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_5M/* asciiTab15 */ = new T2(1,_5L/* GHC.Show.asciiTab50 */,_5K/* GHC.Show.asciiTab16 */),
_5N/* asciiTab51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_5O/* asciiTab14 */ = new T2(1,_5N/* GHC.Show.asciiTab51 */,_5M/* GHC.Show.asciiTab15 */),
_5P/* asciiTab52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_5Q/* asciiTab13 */ = new T2(1,_5P/* GHC.Show.asciiTab52 */,_5O/* GHC.Show.asciiTab14 */),
_5R/* asciiTab53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_5S/* asciiTab12 */ = new T2(1,_5R/* GHC.Show.asciiTab53 */,_5Q/* GHC.Show.asciiTab13 */),
_5T/* asciiTab54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_5U/* asciiTab11 */ = new T2(1,_5T/* GHC.Show.asciiTab54 */,_5S/* GHC.Show.asciiTab12 */),
_5V/* asciiTab55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_5W/* asciiTab10 */ = new T2(1,_5V/* GHC.Show.asciiTab55 */,_5U/* GHC.Show.asciiTab11 */),
_5X/* asciiTab56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_5Y/* asciiTab9 */ = new T2(1,_5X/* GHC.Show.asciiTab56 */,_5W/* GHC.Show.asciiTab10 */),
_5Z/* asciiTab8 */ = new T2(1,_5c/* GHC.Show.asciiTab57 */,_5Y/* GHC.Show.asciiTab9 */),
_60/* asciiTab7 */ = new T2(1,_5b/* GHC.Show.asciiTab58 */,_5Z/* GHC.Show.asciiTab8 */),
_61/* asciiTab6 */ = new T2(1,_5a/* GHC.Show.asciiTab59 */,_60/* GHC.Show.asciiTab7 */),
_62/* asciiTab60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_63/* asciiTab5 */ = new T2(1,_62/* GHC.Show.asciiTab60 */,_61/* GHC.Show.asciiTab6 */),
_64/* asciiTab61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_65/* asciiTab4 */ = new T2(1,_64/* GHC.Show.asciiTab61 */,_63/* GHC.Show.asciiTab5 */),
_66/* asciiTab62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_67/* asciiTab3 */ = new T2(1,_66/* GHC.Show.asciiTab62 */,_65/* GHC.Show.asciiTab4 */),
_68/* asciiTab63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_69/* asciiTab2 */ = new T2(1,_68/* GHC.Show.asciiTab63 */,_67/* GHC.Show.asciiTab3 */),
_6a/* asciiTab64 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_6b/* asciiTab1 */ = new T2(1,_6a/* GHC.Show.asciiTab64 */,_69/* GHC.Show.asciiTab2 */),
_6c/* asciiTab65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_6d/* asciiTab */ = new T2(1,_6c/* GHC.Show.asciiTab65 */,_6b/* GHC.Show.asciiTab1 */),
_6e/* lvl */ = 92,
_6f/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\DEL"));
}),
_6g/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\a"));
}),
_6h/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\\"));
}),
_6i/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\SO"));
}),
_6j/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\r"));
}),
_6k/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\f"));
}),
_6l/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\v"));
}),
_6m/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\n"));
}),
_6n/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\t"));
}),
_6o/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\b"));
}),
_6p/* $wshowLitChar */ = function(_6q/* sfeh */, _6r/* sfei */){
  if(_6q/* sfeh */<=127){
    var _6s/* sfel */ = E(_6q/* sfeh */);
    switch(_6s/* sfel */){
      case 92:
        return new F(function(){return _12/* GHC.Base.++ */(_6h/* GHC.Show.lvl2 */, _6r/* sfei */);});
        break;
      case 127:
        return new F(function(){return _12/* GHC.Base.++ */(_6f/* GHC.Show.lvl1 */, _6r/* sfei */);});
        break;
      default:
        if(_6s/* sfel */<32){
          var _6t/* sfeo */ = E(_6s/* sfel */);
          switch(_6t/* sfeo */){
            case 7:
              return new F(function(){return _12/* GHC.Base.++ */(_6g/* GHC.Show.lvl10 */, _6r/* sfei */);});
              break;
            case 8:
              return new F(function(){return _12/* GHC.Base.++ */(_6o/* GHC.Show.lvl9 */, _6r/* sfei */);});
              break;
            case 9:
              return new F(function(){return _12/* GHC.Base.++ */(_6n/* GHC.Show.lvl8 */, _6r/* sfei */);});
              break;
            case 10:
              return new F(function(){return _12/* GHC.Base.++ */(_6m/* GHC.Show.lvl7 */, _6r/* sfei */);});
              break;
            case 11:
              return new F(function(){return _12/* GHC.Base.++ */(_6l/* GHC.Show.lvl6 */, _6r/* sfei */);});
              break;
            case 12:
              return new F(function(){return _12/* GHC.Base.++ */(_6k/* GHC.Show.lvl5 */, _6r/* sfei */);});
              break;
            case 13:
              return new F(function(){return _12/* GHC.Base.++ */(_6j/* GHC.Show.lvl4 */, _6r/* sfei */);});
              break;
            case 14:
              return new F(function(){return _12/* GHC.Base.++ */(_6i/* GHC.Show.lvl3 */, new T(function(){
                var _6u/* sfes */ = E(_6r/* sfei */);
                if(!_6u/* sfes */._){
                  return __Z/* EXTERNAL */;
                }else{
                  if(E(_6u/* sfes */.a)==72){
                    return B(unAppCStr/* EXTERNAL */("\\&", _6u/* sfes */));
                  }else{
                    return E(_6u/* sfes */);
                  }
                }
              },1));});
              break;
            default:
              return new F(function(){return _12/* GHC.Base.++ */(new T2(1,_6e/* GHC.Show.lvl */,new T(function(){
                return B(_57/* GHC.List.$w!! */(_6d/* GHC.Show.asciiTab */, _6t/* sfeo */));
              })), _6r/* sfei */);});
          }
        }else{
          return new T2(1,_6s/* sfel */,_6r/* sfei */);
        }
    }
  }else{
    var _6v/* sfeR */ = new T(function(){
      var _6w/* sfeC */ = jsShowI/* EXTERNAL */(_6q/* sfeh */);
      return B(_12/* GHC.Base.++ */(fromJSStr/* EXTERNAL */(_6w/* sfeC */), new T(function(){
        var _6x/* sfeH */ = E(_6r/* sfei */);
        if(!_6x/* sfeH */._){
          return __Z/* EXTERNAL */;
        }else{
          var _6y/* sfeK */ = E(_6x/* sfeH */.a);
          if(_6y/* sfeK */<48){
            return E(_6x/* sfeH */);
          }else{
            if(_6y/* sfeK */>57){
              return E(_6x/* sfeH */);
            }else{
              return B(unAppCStr/* EXTERNAL */("\\&", _6x/* sfeH */));
            }
          }
        }
      },1)));
    });
    return new T2(1,_6e/* GHC.Show.lvl */,_6v/* sfeR */);
  }
},
_6z/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\\""));
}),
_6A/* showLitString */ = function(_6B/* sfeW */, _6C/* sfeX */){
  var _6D/* sfeY */ = E(_6B/* sfeW */);
  if(!_6D/* sfeY */._){
    return E(_6C/* sfeX */);
  }else{
    var _6E/* sff0 */ = _6D/* sfeY */.b,
    _6F/* sff3 */ = E(_6D/* sfeY */.a);
    if(_6F/* sff3 */==34){
      return new F(function(){return _12/* GHC.Base.++ */(_6z/* GHC.Show.lvl11 */, new T(function(){
        return B(_6A/* GHC.Show.showLitString */(_6E/* sff0 */, _6C/* sfeX */));
      },1));});
    }else{
      return new F(function(){return _6p/* GHC.Show.$wshowLitChar */(_6F/* sff3 */, new T(function(){
        return B(_6A/* GHC.Show.showLitString */(_6E/* sff0 */, _6C/* sfeX */));
      }));});
    }
  }
},
_6G/* $fShowFormElement_$cshow */ = function(_6H/* s5Vn */){
  var _6I/* s5Vo */ = E(_6H/* s5Vn */);
  switch(_6I/* s5Vo */._){
    case 0:
      var _6J/* s5VF */ = new T(function(){
        var _6K/* s5VE */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_4t/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_6L/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _6I/* s5Vo */.b, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), _6K/* s5VE */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4p/* FormEngine.FormElement.FormElement.lvl15 */, _6J/* s5VF */);});
      break;
    case 1:
      var _6M/* s5VV */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_4w/* FormEngine.FormElement.FormElement.lvl6 */, _6I/* s5Vo */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4o/* FormEngine.FormElement.FormElement.lvl14 */, _6M/* s5VV */);});
      break;
    case 2:
      var _6N/* s5Wb */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_4w/* FormEngine.FormElement.FormElement.lvl6 */, _6I/* s5Vo */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4n/* FormEngine.FormElement.FormElement.lvl13 */, _6N/* s5Wb */);});
      break;
    case 3:
      var _6O/* s5Wr */ = new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), new T(function(){
          return B(_12/* GHC.Base.++ */(_4w/* FormEngine.FormElement.FormElement.lvl6 */, _6I/* s5Vo */.b));
        },1)));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4m/* FormEngine.FormElement.FormElement.lvl12 */, _6O/* s5Wr */);});
      break;
    case 4:
      var _6P/* s5WV */ = new T(function(){
        var _6Q/* s5WU */ = new T(function(){
          var _6R/* s5WT */ = new T(function(){
            var _6S/* s5WH */ = new T(function(){
              var _6T/* s5WM */ = new T(function(){
                var _6U/* s5WI */ = E(_6I/* s5Vo */.c);
                if(!_6U/* s5WI */._){
                  return E(_43/* GHC.Show.$fShowMaybe3 */);
                }else{
                  return B(_12/* GHC.Base.++ */(_42/* GHC.Show.$fShowMaybe1 */, new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
                    return B(_6A/* GHC.Show.showLitString */(_6U/* s5WI */.a, _4r/* FormEngine.FormElement.FormElement.lvl16 */));
                  }))));
                }
              },1);
              return B(_12/* GHC.Base.++ */(_4k/* FormEngine.FormElement.FormElement.lvl10 */, _6T/* s5WM */));
            }),
            _6V/* s5WN */ = E(_6I/* s5Vo */.b);
            if(!_6V/* s5WN */._){
              return B(_12/* GHC.Base.++ */(_43/* GHC.Show.$fShowMaybe3 */, _6S/* s5WH */));
            }else{
              return B(_12/* GHC.Base.++ */(_42/* GHC.Show.$fShowMaybe1 */, new T(function(){
                return B(_12/* GHC.Base.++ */(B(_4a/* GHC.Show.$wshowSignedInt */(11, E(_6V/* s5WN */.a), _I/* GHC.Types.[] */)), _6S/* s5WH */));
              },1)));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_4w/* FormEngine.FormElement.FormElement.lvl6 */, _6R/* s5WT */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), _6Q/* s5WU */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4l/* FormEngine.FormElement.FormElement.lvl11 */, _6P/* s5WV */);});
      break;
    case 5:
      return new F(function(){return _12/* GHC.Base.++ */(_4z/* FormEngine.FormElement.FormElement.lvl9 */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b));
      },1));});
      break;
    case 6:
      return new F(function(){return _12/* GHC.Base.++ */(_4y/* FormEngine.FormElement.FormElement.lvl8 */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b));
      },1));});
      break;
    case 7:
      var _6W/* s5XH */ = new T(function(){
        var _6X/* s5XG */ = new T(function(){
          var _6Y/* s5XF */ = new T(function(){
            var _6Z/* s5XB */ = E(_6I/* s5Vo */.b);
            if(!_6Z/* s5XB */._){
              return E(_43/* GHC.Show.$fShowMaybe3 */);
            }else{
              return B(_12/* GHC.Base.++ */(_42/* GHC.Show.$fShowMaybe1 */, new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
                return B(_6A/* GHC.Show.showLitString */(_6Z/* s5XB */.a, _4r/* FormEngine.FormElement.FormElement.lvl16 */));
              }))));
            }
          },1);
          return B(_12/* GHC.Base.++ */(_4w/* FormEngine.FormElement.FormElement.lvl6 */, _6Y/* s5XF */));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), _6X/* s5XG */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4x/* FormEngine.FormElement.FormElement.lvl7 */, _6W/* s5XH */);});
      break;
    case 8:
      var _70/* s5XY */ = new T(function(){
        var _71/* s5XX */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_4t/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_6L/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _6I/* s5Vo */.b, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), _71/* s5XX */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4v/* FormEngine.FormElement.FormElement.lvl5 */, _70/* s5XY */);});
      break;
    case 9:
      var _72/* s5Yg */ = new T(function(){
        var _73/* s5Yf */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_4t/* FormEngine.FormElement.FormElement.lvl3 */, new T(function(){
            return B(_26/* GHC.Show.showList__ */(_6L/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _6I/* s5Vo */.c, _I/* GHC.Types.[] */));
          },1)));
        },1);
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b)), _73/* s5Yf */));
      },1);
      return new F(function(){return _12/* GHC.Base.++ */(_4u/* FormEngine.FormElement.FormElement.lvl4 */, _72/* s5Yg */);});
      break;
    case 10:
      return new F(function(){return _12/* GHC.Base.++ */(_4s/* FormEngine.FormElement.FormElement.lvl2 */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b));
      },1));});
      break;
    case 11:
      return new F(function(){return _12/* GHC.Base.++ */(_4j/* FormEngine.FormElement.FormElement.lvl1 */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b));
      },1));});
      break;
    default:
      return new F(function(){return _12/* GHC.Base.++ */(_4i/* FormEngine.FormElement.FormElement.lvl */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_6I/* s5Vo */.a)).b));
      },1));});
  }
},
_6L/* $fShowFormElement1 */ = function(_74/* s5Vk */, _75/* s5Vl */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_6G/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_74/* s5Vk */)), _75/* s5Vl */);});
},
_76/* appearJq5 */ = "(function (key, val, jq) { jq.css(key, val); return jq; })",
_77/* $wa2 */ = function(_78/* so3v */, _79/* so3w */, _7a/* so3x */, _/* EXTERNAL */){
  var _7b/* so3M */ = eval/* EXTERNAL */(E(_76/* FormEngine.JQuery.appearJq5 */));
  return new F(function(){return E(_7b/* so3M */)(toJSStr/* EXTERNAL */(E(_78/* so3v */)), toJSStr/* EXTERNAL */(E(_79/* so3w */)), _7a/* so3x */);});
},
_7c/* toPx1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("px"));
}),
_7d/* $wtoPx */ = function(_7e/* snzE */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4a/* GHC.Show.$wshowSignedInt */(0, _7e/* snzE */, _I/* GHC.Types.[] */)), _7c/* FormEngine.JQuery.toPx1 */);});
},
_7f/* descSubpaneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane"));
}),
_7g/* elemChapter */ = function(_7h/* s61e */){
  while(1){
    var _7i/* s61f */ = E(_7h/* s61e */);
    switch(_7i/* s61f */._){
      case 0:
        return E(_7i/* s61f */);
      case 1:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 2:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 3:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 4:
        _7h/* s61e */ = _7i/* s61f */.d;
        continue;
      case 5:
        _7h/* s61e */ = _7i/* s61f */.b;
        continue;
      case 6:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 7:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 8:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 9:
        _7h/* s61e */ = _7i/* s61f */.d;
        continue;
      case 10:
        _7h/* s61e */ = _7i/* s61f */.c;
        continue;
      case 11:
        _7h/* s61e */ = _7i/* s61f */.b;
        continue;
      default:
        _7h/* s61e */ = _7i/* s61f */.b;
        continue;
    }
  }
},
_7j/* formItem */ = function(_7k/* s5SV */){
  var _7l/* s5SW */ = E(_7k/* s5SV */);
  switch(_7l/* s5SW */._){
    case 0:
      return E(_7l/* s5SW */.a);
    case 1:
      return E(_7l/* s5SW */.a);
    case 2:
      return E(_7l/* s5SW */.a);
    case 3:
      return E(_7l/* s5SW */.a);
    case 4:
      return E(_7l/* s5SW */.a);
    case 5:
      return E(_7l/* s5SW */.a);
    case 6:
      return E(_7l/* s5SW */.a);
    case 7:
      return E(_7l/* s5SW */.a);
    case 8:
      return E(_7l/* s5SW */.a);
    case 9:
      return E(_7l/* s5SW */.a);
    case 10:
      return E(_7l/* s5SW */.a);
    case 11:
      return E(_7l/* s5SW */.a);
    default:
      return E(_7l/* s5SW */.a);
  }
},
_7m/* descSubpaneId */ = function(_7n/* skBM */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(B(_7g/* FormEngine.FormElement.FormElement.elemChapter */(_7n/* skBM */)))))).b)), _7f/* FormEngine.FormElement.Identifiers.descSubpaneId1 */);});
},
_7o/* getScrollTop_f1 */ = new T(function(){
  return (function (jq) { return jq.scrollTop(); });
}),
_7p/* getTop_f1 */ = new T(function(){
  return (function (jq) { return jq.position().top; });
}),
_7q/* getWindow_f1 */ = new T(function(){
  return (function () { return $(window); });
}),
_7r/* isVisible_f1 */ = new T(function(){
  return (function (jq) { return jq.is(':visible'); });
}),
_7s/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_7t/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_7u/* select2 */ = "(function (elId) { var res = $(elId); if (res.length === 0) { console.warn(\'empty $ selection \' + elId); }; return res; })",
_7v/* select1 */ = function(_7w/* snVJ */, _/* EXTERNAL */){
  var _7x/* snVT */ = eval/* EXTERNAL */(E(_7u/* FormEngine.JQuery.select2 */));
  return new F(function(){return E(_7x/* snVT */)(toJSStr/* EXTERNAL */(E(_7w/* snVJ */)));});
},
_7y/* $wa1 */ = function(_7z/* sibX */, _/* EXTERNAL */){
  var _7A/* sibZ */ = E(_7z/* sibX */);
  if(!_7A/* sibZ */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _7B/* sic2 */ = B(_12/* GHC.Base.++ */(_7t/* Main.lvl2 */, new T(function(){
      return B(_7m/* FormEngine.FormElement.Identifiers.descSubpaneId */(_7A/* sibZ */.a));
    },1))),
    _7C/* sic4 */ = B(_7v/* FormEngine.JQuery.select1 */(_7B/* sic2 */, _/* EXTERNAL */)),
    _7D/* sic9 */ = E(_7r/* FormEngine.JQuery.isVisible_f1 */),
    _7E/* sicc */ = __app1/* EXTERNAL */(_7D/* sic9 */, E(_7C/* sic4 */)),
    _7F/* sicf */ = function(_7G/* sicg */, _/* EXTERNAL */){
      var _7H/* sici */ = E(_7G/* sicg */);
      if(!_7H/* sici */._){
        return _I/* GHC.Types.[] */;
      }else{
        var _7I/* sicl */ = B(_12/* GHC.Base.++ */(_7t/* Main.lvl2 */, new T(function(){
          return B(_7m/* FormEngine.FormElement.Identifiers.descSubpaneId */(_7H/* sici */.a));
        },1))),
        _7J/* sicn */ = B(_7v/* FormEngine.JQuery.select1 */(_7I/* sicl */, _/* EXTERNAL */)),
        _7K/* sict */ = __app1/* EXTERNAL */(_7D/* sic9 */, E(_7J/* sicn */)),
        _7L/* sicw */ = B(_7F/* sicf */(_7H/* sici */.b, _/* EXTERNAL */));
        return new T(function(){
          if(!_7K/* sict */){
            return E(_7L/* sicw */);
          }else{
            return new T2(1,_7I/* sicl */,_7L/* sicw */);
          }
        });
      }
    },
    _7M/* sicB */ = B(_7F/* sicf */(_7A/* sibZ */.b, _/* EXTERNAL */)),
    _7N/* sicE */ = function(_7O/* sicF */, _7P/* sicG */){
      var _7Q/* sicH */ = B(_7v/* FormEngine.JQuery.select1 */(_7O/* sicF */, _/* EXTERNAL */)),
      _7R/* sicN */ = __app0/* EXTERNAL */(E(_7q/* FormEngine.JQuery.getWindow_f1 */)),
      _7S/* sicT */ = __app1/* EXTERNAL */(E(_7o/* FormEngine.JQuery.getScrollTop_f1 */), _7R/* sicN */),
      _7T/* sicW */ = E(_7Q/* sicH */),
      _7U/* sid1 */ = __app1/* EXTERNAL */(E(_7p/* FormEngine.JQuery.getTop_f1 */), _7T/* sicW */),
      _7V/* sid5 */ = Number/* EXTERNAL */(_7S/* sicT */),
      _7W/* sid9 */ = jsTrunc/* EXTERNAL */(_7V/* sid5 */),
      _7X/* sidd */ = Number/* EXTERNAL */(_7U/* sid1 */),
      _7Y/* sidh */ = jsTrunc/* EXTERNAL */(_7X/* sidd */),
      _7Z/* sidk */ = _7W/* sid9 */-_7Y/* sidh */|0;
      if(_7Z/* sidk */<=0){
        return _0/* GHC.Tuple.() */;
      }else{
        var _80/* sido */ = B(_77/* FormEngine.JQuery.$wa2 */(_7s/* Main.lvl1 */, B(_7d/* FormEngine.JQuery.$wtoPx */(_7Z/* sidk */)), _7T/* sicW */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      }
    };
    if(!_7E/* sicc */){
      var _81/* sids */ = E(_7M/* sicB */);
      if(!_81/* sids */._){
        return _0/* GHC.Tuple.() */;
      }else{
        return new F(function(){return _7N/* sicE */(_81/* sids */.a, _81/* sids */.b);});
      }
    }else{
      return new F(function(){return _7N/* sicE */(_7B/* sic2 */, _7M/* sicB */);});
    }
  }
},
_82/* resize2 */ = "(function (jq) { jq.resize(); })",
_83/* $wa17 */ = function(_84/* snBP */, _/* EXTERNAL */){
  var _85/* snBU */ = eval/* EXTERNAL */(E(_82/* FormEngine.JQuery.resize2 */)),
  _86/* snC2 */ = E(_85/* snBU */)(_84/* snBP */);
  return _84/* snBP */;
},
_87/* catMaybes1 */ = function(_88/*  s7rA */){
  while(1){
    var _89/*  catMaybes1 */ = B((function(_8a/* s7rA */){
      var _8b/* s7rB */ = E(_8a/* s7rA */);
      if(!_8b/* s7rB */._){
        return __Z/* EXTERNAL */;
      }else{
        var _8c/* s7rD */ = _8b/* s7rB */.b,
        _8d/* s7rE */ = E(_8b/* s7rB */.a);
        if(!_8d/* s7rE */._){
          _88/*  s7rA */ = _8c/* s7rD */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_8d/* s7rE */.a,new T(function(){
            return B(_87/* Data.Maybe.catMaybes1 */(_8c/* s7rD */));
          }));
        }
      }
    })(_88/*  s7rA */));
    if(_89/*  catMaybes1 */!=__continue/* EXTERNAL */){
      return _89/*  catMaybes1 */;
    }
  }
},
_8e/* dumptIO2 */ = "(function (s) { console.log(s); })",
_8f/* dumptIO1 */ = function(_8g/* snK8 */, _/* EXTERNAL */){
  var _8h/* snKi */ = eval/* EXTERNAL */(E(_8e/* FormEngine.JQuery.dumptIO2 */)),
  _8i/* snKq */ = E(_8h/* snKi */)(toJSStr/* EXTERNAL */(E(_8g/* snK8 */)));
  return _0/* GHC.Tuple.() */;
},
_8j/* errorIO2 */ = "(function (s) { console.error(s); })",
_8k/* errorIO1 */ = function(_8l/* snKt */, _/* EXTERNAL */){
  var _8m/* snKD */ = eval/* EXTERNAL */(E(_8j/* FormEngine.JQuery.errorIO2 */)),
  _8n/* snKL */ = E(_8m/* snKD */)(toJSStr/* EXTERNAL */(E(_8l/* snKt */)));
  return _0/* GHC.Tuple.() */;
},
_8o/* $fShowNumbering2 */ = 0,
_8p/* $wgo2 */ = function(_8q/*  s5o4 */, _8r/*  s5o5 */, _8s/*  s5o6 */){
  while(1){
    var _8t/*  $wgo2 */ = B((function(_8u/* s5o4 */, _8v/* s5o5 */, _8w/* s5o6 */){
      var _8x/* s5o7 */ = E(_8u/* s5o4 */);
      if(!_8x/* s5o7 */._){
        return new T2(0,_8v/* s5o5 */,_8w/* s5o6 */);
      }else{
        var _8y/* s5o8 */ = _8x/* s5o7 */.a,
        _8z/* s5oj */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_8w/* s5o6 */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8v/* s5o5 */, _8y/* s5o8 */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _8q/*  s5o4 */ = _8x/* s5o7 */.b;
        _8r/*  s5o5 */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8v/* s5o5 */, _8y/* s5o8 */)).a);
        });
        _8s/*  s5o6 */ = _8z/* s5oj */;
        return __continue/* EXTERNAL */;
      }
    })(_8q/*  s5o4 */, _8r/*  s5o5 */, _8s/*  s5o6 */));
    if(_8t/*  $wgo2 */!=__continue/* EXTERNAL */){
      return _8t/*  $wgo2 */;
    }
  }
},
_8B/* $wgo3 */ = function(_8C/*  s5ok */, _8D/*  s5ol */, _8E/*  s5om */){
  while(1){
    var _8F/*  $wgo3 */ = B((function(_8G/* s5ok */, _8H/* s5ol */, _8I/* s5om */){
      var _8J/* s5on */ = E(_8G/* s5ok */);
      if(!_8J/* s5on */._){
        return new T2(0,_8H/* s5ol */,_8I/* s5om */);
      }else{
        var _8K/* s5oo */ = _8J/* s5on */.a,
        _8L/* s5oz */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_8I/* s5om */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8H/* s5ol */, _8K/* s5oo */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _8C/*  s5ok */ = _8J/* s5on */.b;
        _8D/*  s5ol */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8H/* s5ol */, _8K/* s5oo */)).a);
        });
        _8E/*  s5om */ = _8L/* s5oz */;
        return __continue/* EXTERNAL */;
      }
    })(_8C/*  s5ok */, _8D/*  s5ol */, _8E/*  s5om */));
    if(_8F/*  $wgo3 */!=__continue/* EXTERNAL */){
      return _8F/*  $wgo3 */;
    }
  }
},
_8M/* $wgo4 */ = function(_8N/*  s5oA */, _8O/*  s5oB */, _8P/*  s5oC */){
  while(1){
    var _8Q/*  $wgo4 */ = B((function(_8R/* s5oA */, _8S/* s5oB */, _8T/* s5oC */){
      var _8U/* s5oD */ = E(_8R/* s5oA */);
      if(!_8U/* s5oD */._){
        return new T2(0,_8S/* s5oB */,_8T/* s5oC */);
      }else{
        var _8V/* s5oE */ = _8U/* s5oD */.a,
        _8W/* s5oP */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_8T/* s5oC */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8S/* s5oB */, _8V/* s5oE */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _8N/*  s5oA */ = _8U/* s5oD */.b;
        _8O/*  s5oB */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_8S/* s5oB */, _8V/* s5oE */)).a);
        });
        _8P/*  s5oC */ = _8W/* s5oP */;
        return __continue/* EXTERNAL */;
      }
    })(_8N/*  s5oA */, _8O/*  s5oB */, _8P/*  s5oC */));
    if(_8Q/*  $wgo4 */!=__continue/* EXTERNAL */){
      return _8Q/*  $wgo4 */;
    }
  }
},
_8X/* $wgo5 */ = function(_8Y/*  s5oQ */, _8Z/*  s5oR */, _90/*  s5oS */){
  while(1){
    var _91/*  $wgo5 */ = B((function(_92/* s5oQ */, _93/* s5oR */, _94/* s5oS */){
      var _95/* s5oT */ = E(_92/* s5oQ */);
      if(!_95/* s5oT */._){
        return new T2(0,_93/* s5oR */,_94/* s5oS */);
      }else{
        var _96/* s5oU */ = _95/* s5oT */.a,
        _97/* s5p5 */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_94/* s5oS */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_93/* s5oR */, _96/* s5oU */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _8Y/*  s5oQ */ = _95/* s5oT */.b;
        _8Z/*  s5oR */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_93/* s5oR */, _96/* s5oU */)).a);
        });
        _90/*  s5oS */ = _97/* s5p5 */;
        return __continue/* EXTERNAL */;
      }
    })(_8Y/*  s5oQ */, _8Z/*  s5oR */, _90/*  s5oS */));
    if(_91/*  $wgo5 */!=__continue/* EXTERNAL */){
      return _91/*  $wgo5 */;
    }
  }
},
_98/* $wgo6 */ = function(_99/*  s5p6 */, _9a/*  s5p7 */, _9b/*  s5p8 */){
  while(1){
    var _9c/*  $wgo6 */ = B((function(_9d/* s5p6 */, _9e/* s5p7 */, _9f/* s5p8 */){
      var _9g/* s5p9 */ = E(_9d/* s5p6 */);
      if(!_9g/* s5p9 */._){
        return new T2(0,_9e/* s5p7 */,_9f/* s5p8 */);
      }else{
        var _9h/* s5pa */ = _9g/* s5p9 */.a,
        _9i/* s5pl */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_9f/* s5p8 */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_9e/* s5p7 */, _9h/* s5pa */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _99/*  s5p6 */ = _9g/* s5p9 */.b;
        _9a/*  s5p7 */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_9e/* s5p7 */, _9h/* s5pa */)).a);
        });
        _9b/*  s5p8 */ = _9i/* s5pl */;
        return __continue/* EXTERNAL */;
      }
    })(_99/*  s5p6 */, _9a/*  s5p7 */, _9b/*  s5p8 */));
    if(_9c/*  $wgo6 */!=__continue/* EXTERNAL */){
      return _9c/*  $wgo6 */;
    }
  }
},
_9j/* xs */ = new T(function(){
  return new T2(1,_8o/* FormEngine.FormItem.$fShowNumbering2 */,_9j/* FormEngine.FormItem.xs */);
}),
_9k/* incrementAtLevel */ = function(_9l/* s5nH */){
  var _9m/* s5nI */ = E(_9l/* s5nH */);
  if(!_9m/* s5nI */._){
    return __Z/* EXTERNAL */;
  }else{
    var _9n/* s5nJ */ = _9m/* s5nI */.a,
    _9o/* s5nK */ = _9m/* s5nI */.b,
    _9p/* s5o3 */ = new T(function(){
      var _9q/* s5nL */ = E(_9o/* s5nK */),
      _9r/* s5nR */ = new T2(1,new T(function(){
        return B(_57/* GHC.List.$w!! */(_9n/* s5nJ */, _9q/* s5nL */))+1|0;
      }),_9j/* FormEngine.FormItem.xs */);
      if(0>=_9q/* s5nL */){
        return E(_9r/* s5nR */);
      }else{
        var _9s/* s5nU */ = function(_9t/* s5nV */, _9u/* s5nW */){
          var _9v/* s5nX */ = E(_9t/* s5nV */);
          if(!_9v/* s5nX */._){
            return E(_9r/* s5nR */);
          }else{
            var _9w/* s5nY */ = _9v/* s5nX */.a,
            _9x/* s5o0 */ = E(_9u/* s5nW */);
            return (_9x/* s5o0 */==1) ? new T2(1,_9w/* s5nY */,_9r/* s5nR */) : new T2(1,_9w/* s5nY */,new T(function(){
              return B(_9s/* s5nU */(_9v/* s5nX */.b, _9x/* s5o0 */-1|0));
            }));
          }
        };
        return B(_9s/* s5nU */(_9n/* s5nJ */, _9q/* s5nL */));
      }
    });
    return new T2(1,_9p/* s5o3 */,_9o/* s5nK */);
  }
},
_9y/* $wgo7 */ = function(_9z/*  s5pm */, _9A/*  s5pn */, _9B/*  s5po */){
  while(1){
    var _9C/*  $wgo7 */ = B((function(_9D/* s5pm */, _9E/* s5pn */, _9F/* s5po */){
      var _9G/* s5pp */ = E(_9D/* s5pm */);
      if(!_9G/* s5pp */._){
        return new T2(0,_9E/* s5pn */,_9F/* s5po */);
      }else{
        var _9H/* s5pr */ = _9G/* s5pp */.b,
        _9I/* s5ps */ = E(_9G/* s5pp */.a);
        if(!_9I/* s5ps */._){
          var _9J/*   s5pn */ = _9E/* s5pn */;
          _9z/*  s5pm */ = _9H/* s5pr */;
          _9A/*  s5pn */ = _9J/*   s5pn */;
          _9B/*  s5po */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_9F/* s5po */, new T2(1,_9I/* s5ps */,_I/* GHC.Types.[] */)));
          });
          return __continue/* EXTERNAL */;
        }else{
          var _9K/* s5pO */ = new T(function(){
            var _9L/* s5pL */ = new T(function(){
              var _9M/* s5pH */ = new T(function(){
                var _9N/* s5pA */ = E(_9E/* s5pn */);
                if(!_9N/* s5pA */._){
                  return __Z/* EXTERNAL */;
                }else{
                  return new T2(1,_9N/* s5pA */.a,new T(function(){
                    return E(_9N/* s5pA */.b)+1|0;
                  }));
                }
              });
              return E(B(_98/* FormEngine.FormItem.$wgo6 */(_9I/* s5ps */.c, _9M/* s5pH */, _I/* GHC.Types.[] */)).b);
            });
            return B(_12/* GHC.Base.++ */(_9F/* s5po */, new T2(1,new T3(1,_9E/* s5pn */,_9I/* s5ps */.b,_9L/* s5pL */),_I/* GHC.Types.[] */)));
          });
          _9z/*  s5pm */ = _9H/* s5pr */;
          _9A/*  s5pn */ = new T(function(){
            return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9E/* s5pn */));
          });
          _9B/*  s5po */ = _9K/* s5pO */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_9z/*  s5pm */, _9A/*  s5pn */, _9B/*  s5po */));
    if(_9C/*  $wgo7 */!=__continue/* EXTERNAL */){
      return _9C/*  $wgo7 */;
    }
  }
},
_8A/* $wincrementNumbering */ = function(_9O/* s5pP */, _9P/* s5pQ */){
  var _9Q/* s5pR */ = E(_9P/* s5pQ */);
  switch(_9Q/* s5pR */._){
    case 0:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T1(0,new T(function(){
        var _9R/* s5pU */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9R/* s5pU */.a,b:_9O/* s5pP */,c:_9R/* s5pU */.c,d:_9R/* s5pU */.d,e:_9R/* s5pU */.e,f:_9R/* s5pU */.f,g:_9R/* s5pU */.g,h:_9R/* s5pU */.h,i:_9R/* s5pU */.i};
      })));
    case 1:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T1(1,new T(function(){
        var _9S/* s5q8 */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9S/* s5q8 */.a,b:_9O/* s5pP */,c:_9S/* s5q8 */.c,d:_9S/* s5q8 */.d,e:_9S/* s5q8 */.e,f:_9S/* s5q8 */.f,g:_9S/* s5q8 */.g,h:_9S/* s5q8 */.h,i:_9S/* s5q8 */.i};
      })));
    case 2:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T1(2,new T(function(){
        var _9T/* s5qm */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9T/* s5qm */.a,b:_9O/* s5pP */,c:_9T/* s5qm */.c,d:_9T/* s5qm */.d,e:_9T/* s5qm */.e,f:_9T/* s5qm */.f,g:_9T/* s5qm */.g,h:_9T/* s5qm */.h,i:_9T/* s5qm */.i};
      })));
    case 3:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T2(3,new T(function(){
        var _9U/* s5qB */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9U/* s5qB */.a,b:_9O/* s5pP */,c:_9U/* s5qB */.c,d:_9U/* s5qB */.d,e:_9U/* s5qB */.e,f:_9U/* s5qB */.f,g:_9U/* s5qB */.g,h:_9U/* s5qB */.h,i:_9U/* s5qB */.i};
      }),_9Q/* s5pR */.b));
    case 4:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T2(4,new T(function(){
        var _9V/* s5qQ */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9V/* s5qQ */.a,b:_9O/* s5pP */,c:_9V/* s5qQ */.c,d:_9V/* s5qQ */.d,e:_9V/* s5qQ */.e,f:_9V/* s5qQ */.f,g:_9V/* s5qQ */.g,h:_9V/* s5qQ */.h,i:_9V/* s5qQ */.i};
      }),_9Q/* s5pR */.b));
    case 5:
      var _9W/* s5rr */ = new T(function(){
        var _9X/* s5rn */ = new T(function(){
          var _9Y/* s5rg */ = E(_9O/* s5pP */);
          if(!_9Y/* s5rg */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_9Y/* s5rg */.a,new T(function(){
              return E(_9Y/* s5rg */.b)+1|0;
            }));
          }
        });
        return E(B(_9y/* FormEngine.FormItem.$wgo7 */(_9Q/* s5pR */.b, _9X/* s5rn */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T2(5,new T(function(){
        var _9Z/* s5r5 */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_9Z/* s5r5 */.a,b:_9O/* s5pP */,c:_9Z/* s5r5 */.c,d:_9Z/* s5r5 */.d,e:_9Z/* s5r5 */.e,f:_9Z/* s5r5 */.f,g:_9Z/* s5r5 */.g,h:_9Z/* s5r5 */.h,i:_9Z/* s5r5 */.i};
      }),_9W/* s5rr */));
    case 6:
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T2(6,new T(function(){
        var _a0/* s5rw */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_a0/* s5rw */.a,b:_9O/* s5pP */,c:_a0/* s5rw */.c,d:_a0/* s5rw */.d,e:_a0/* s5rw */.e,f:_a0/* s5rw */.f,g:_a0/* s5rw */.g,h:_a0/* s5rw */.h,i:_a0/* s5rw */.i};
      }),_9Q/* s5pR */.b));
    case 7:
      var _a1/* s5s7 */ = new T(function(){
        var _a2/* s5s3 */ = new T(function(){
          var _a3/* s5rW */ = E(_9O/* s5pP */);
          if(!_a3/* s5rW */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_a3/* s5rW */.a,new T(function(){
              return E(_a3/* s5rW */.b)+1|0;
            }));
          }
        });
        return E(B(_8X/* FormEngine.FormItem.$wgo5 */(_9Q/* s5pR */.b, _a2/* s5s3 */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T2(7,new T(function(){
        var _a4/* s5rL */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_a4/* s5rL */.a,b:_9O/* s5pP */,c:_a4/* s5rL */.c,d:_a4/* s5rL */.d,e:_a4/* s5rL */.e,f:_a4/* s5rL */.f,g:_a4/* s5rL */.g,h:_a4/* s5rL */.h,i:_a4/* s5rL */.i};
      }),_a1/* s5s7 */));
    case 8:
      var _a5/* s5sD */ = new T(function(){
        var _a6/* s5sz */ = new T(function(){
          var _a7/* s5ss */ = E(_9O/* s5pP */);
          if(!_a7/* s5ss */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_a7/* s5ss */.a,new T(function(){
              return E(_a7/* s5ss */.b)+1|0;
            }));
          }
        });
        return E(B(_8M/* FormEngine.FormItem.$wgo4 */(_9Q/* s5pR */.c, _a6/* s5sz */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T3(8,new T(function(){
        var _a8/* s5sd */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_a8/* s5sd */.a,b:_9O/* s5pP */,c:_a8/* s5sd */.c,d:_a8/* s5sd */.d,e:_a8/* s5sd */.e,f:_a8/* s5sd */.f,g:_a8/* s5sd */.g,h:_a8/* s5sd */.h,i:_a8/* s5sd */.i};
      }),new T(function(){
        var _a9/* s5so */ = E(_9O/* s5pP */);
        if(!_a9/* s5so */._){
          return E(_8o/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_a9/* s5so */.b);
        }
      }),_a5/* s5sD */));
    case 9:
      var _aa/* s5t9 */ = new T(function(){
        var _ab/* s5t5 */ = new T(function(){
          var _ac/* s5sY */ = E(_9O/* s5pP */);
          if(!_ac/* s5sY */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_ac/* s5sY */.a,new T(function(){
              return E(_ac/* s5sY */.b)+1|0;
            }));
          }
        });
        return E(B(_8B/* FormEngine.FormItem.$wgo3 */(_9Q/* s5pR */.c, _ab/* s5t5 */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T3(9,new T(function(){
        var _ad/* s5sJ */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_ad/* s5sJ */.a,b:_9O/* s5pP */,c:_ad/* s5sJ */.c,d:_ad/* s5sJ */.d,e:_ad/* s5sJ */.e,f:_ad/* s5sJ */.f,g:_ad/* s5sJ */.g,h:_ad/* s5sJ */.h,i:_ad/* s5sJ */.i};
      }),new T(function(){
        var _ae/* s5sU */ = E(_9O/* s5pP */);
        if(!_ae/* s5sU */._){
          return E(_8o/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_ae/* s5sU */.b);
        }
      }),_aa/* s5t9 */));
    case 10:
      var _af/* s5tF */ = new T(function(){
        var _ag/* s5tB */ = new T(function(){
          var _ah/* s5tu */ = E(_9O/* s5pP */);
          if(!_ah/* s5tu */._){
            return __Z/* EXTERNAL */;
          }else{
            return new T2(1,_ah/* s5tu */.a,new T(function(){
              return E(_ah/* s5tu */.b)+1|0;
            }));
          }
        });
        return E(B(_8p/* FormEngine.FormItem.$wgo2 */(_9Q/* s5pR */.c, _ag/* s5tB */, _I/* GHC.Types.[] */)).b);
      });
      return new T2(0,new T(function(){
        return B(_9k/* FormEngine.FormItem.incrementAtLevel */(_9O/* s5pP */));
      }),new T3(10,new T(function(){
        var _ai/* s5tf */ = E(_9Q/* s5pR */.a);
        return {_:0,a:_ai/* s5tf */.a,b:_9O/* s5pP */,c:_ai/* s5tf */.c,d:_ai/* s5tf */.d,e:_ai/* s5tf */.e,f:_ai/* s5tf */.f,g:_ai/* s5tf */.g,h:_ai/* s5tf */.h,i:_ai/* s5tf */.i};
      }),new T(function(){
        var _aj/* s5tq */ = E(_9O/* s5pP */);
        if(!_aj/* s5tq */._){
          return E(_8o/* FormEngine.FormItem.$fShowNumbering2 */);
        }else{
          return E(_aj/* s5tq */.b);
        }
      }),_af/* s5tF */));
    default:
      return new T2(0,_9O/* s5pP */,_9Q/* s5pR */);
  }
},
_ak/* $wgo1 */ = function(_al/*  s5w1 */, _am/*  s5w2 */, _an/*  s5w3 */){
  while(1){
    var _ao/*  $wgo1 */ = B((function(_ap/* s5w1 */, _aq/* s5w2 */, _ar/* s5w3 */){
      var _as/* s5w4 */ = E(_ap/* s5w1 */);
      if(!_as/* s5w4 */._){
        return new T2(0,_aq/* s5w2 */,_ar/* s5w3 */);
      }else{
        var _at/* s5w5 */ = _as/* s5w4 */.a,
        _au/* s5wg */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_ar/* s5w3 */, new T2(1,new T(function(){
            return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_aq/* s5w2 */, _at/* s5w5 */)).b);
          }),_I/* GHC.Types.[] */)));
        });
        _al/*  s5w1 */ = _as/* s5w4 */.b;
        _am/*  s5w2 */ = new T(function(){
          return E(B(_8A/* FormEngine.FormItem.$wincrementNumbering */(_aq/* s5w2 */, _at/* s5w5 */)).a);
        });
        _an/*  s5w3 */ = _au/* s5wg */;
        return __continue/* EXTERNAL */;
      }
    })(_al/*  s5w1 */, _am/*  s5w2 */, _an/*  s5w3 */));
    if(_ao/*  $wgo1 */!=__continue/* EXTERNAL */){
      return _ao/*  $wgo1 */;
    }
  }
},
_av/* NoNumbering */ = __Z/* EXTERNAL */,
_aw/* remark5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Your comments"));
}),
_ax/* remark4 */ = new T1(1,_aw/* FormStructure.Common.remark5 */),
_ay/* remark3 */ = {_:0,a:_ax/* FormStructure.Common.remark4 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_az/* remark2 */ = new T1(1,_ay/* FormStructure.Common.remark3 */),
_aA/* remark1 */ = new T2(1,_az/* FormStructure.Common.remark2 */,_I/* GHC.Types.[] */),
_aB/* remark6 */ = 0,
_aC/* True */ = true,
_aD/* remark9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Other"));
}),
_aE/* remark8 */ = new T1(1,_aD/* FormStructure.Common.remark9 */),
_aF/* remark7 */ = {_:0,a:_aE/* FormStructure.Common.remark8 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_aG/* remark */ = new T3(8,_aF/* FormStructure.Common.remark7 */,_aB/* FormStructure.Common.remark6 */,_aA/* FormStructure.Common.remark1 */),
_aH/* ch0GeneralInformation3 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_aI/* ch0GeneralInformation43 */ = 0,
_aJ/* ch0GeneralInformation46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Affiliation"));
}),
_aK/* ch0GeneralInformation45 */ = new T1(1,_aJ/* FormStructure.Chapter0.ch0GeneralInformation46 */),
_aL/* ch0GeneralInformation44 */ = {_:0,a:_aK/* FormStructure.Chapter0.ch0GeneralInformation45 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_aM/* ch0GeneralInformation42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Country"));
}),
_aN/* ch0GeneralInformation41 */ = new T1(1,_aM/* FormStructure.Chapter0.ch0GeneralInformation42 */),
_aO/* ch0GeneralInformation40 */ = {_:0,a:_aN/* FormStructure.Chapter0.ch0GeneralInformation41 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_aP/* countries770 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("France"));
}),
_aQ/* countries771 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FR"));
}),
_aR/* countries769 */ = new T2(0,_aQ/* Countries.countries771 */,_aP/* Countries.countries770 */),
_aS/* countries767 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Guiana"));
}),
_aT/* countries768 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GF"));
}),
_aU/* countries766 */ = new T2(0,_aT/* Countries.countries768 */,_aS/* Countries.countries767 */),
_aV/* countries764 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Polynesia"));
}),
_aW/* countries765 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PF"));
}),
_aX/* countries763 */ = new T2(0,_aW/* Countries.countries765 */,_aV/* Countries.countries764 */),
_aY/* countries761 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("French Southern Territories"));
}),
_aZ/* countries762 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TF"));
}),
_b0/* countries760 */ = new T2(0,_aZ/* Countries.countries762 */,_aY/* Countries.countries761 */),
_b1/* countries758 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gabon"));
}),
_b2/* countries759 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GA"));
}),
_b3/* countries757 */ = new T2(0,_b2/* Countries.countries759 */,_b1/* Countries.countries758 */),
_b4/* countries755 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gambia"));
}),
_b5/* countries756 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GM"));
}),
_b6/* countries754 */ = new T2(0,_b5/* Countries.countries756 */,_b4/* Countries.countries755 */),
_b7/* countries752 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Georgia"));
}),
_b8/* countries753 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GE"));
}),
_b9/* countries751 */ = new T2(0,_b8/* Countries.countries753 */,_b7/* Countries.countries752 */),
_ba/* countries749 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Germany"));
}),
_bb/* countries750 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DE"));
}),
_bc/* countries748 */ = new T2(0,_bb/* Countries.countries750 */,_ba/* Countries.countries749 */),
_bd/* countries746 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ghana"));
}),
_be/* countries747 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GH"));
}),
_bf/* countries745 */ = new T2(0,_be/* Countries.countries747 */,_bd/* Countries.countries746 */),
_bg/* countries743 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Gibraltar"));
}),
_bh/* countries744 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GI"));
}),
_bi/* countries742 */ = new T2(0,_bh/* Countries.countries744 */,_bg/* Countries.countries743 */),
_bj/* countries740 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greece"));
}),
_bk/* countries741 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GR"));
}),
_bl/* countries739 */ = new T2(0,_bk/* Countries.countries741 */,_bj/* Countries.countries740 */),
_bm/* countries737 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Greenland"));
}),
_bn/* countries738 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GL"));
}),
_bo/* countries736 */ = new T2(0,_bn/* Countries.countries738 */,_bm/* Countries.countries737 */),
_bp/* countries734 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Grenada"));
}),
_bq/* countries735 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GD"));
}),
_br/* countries733 */ = new T2(0,_bq/* Countries.countries735 */,_bp/* Countries.countries734 */),
_bs/* countries731 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guadeloupe"));
}),
_bt/* countries732 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GP"));
}),
_bu/* countries730 */ = new T2(0,_bt/* Countries.countries732 */,_bs/* Countries.countries731 */),
_bv/* countries728 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guam"));
}),
_bw/* countries729 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GU"));
}),
_bx/* countries727 */ = new T2(0,_bw/* Countries.countries729 */,_bv/* Countries.countries728 */),
_by/* countries725 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guatemala"));
}),
_bz/* countries726 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GT"));
}),
_bA/* countries724 */ = new T2(0,_bz/* Countries.countries726 */,_by/* Countries.countries725 */),
_bB/* countries722 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guernsey"));
}),
_bC/* countries723 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GG"));
}),
_bD/* countries721 */ = new T2(0,_bC/* Countries.countries723 */,_bB/* Countries.countries722 */),
_bE/* countries719 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea"));
}),
_bF/* countries720 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GN"));
}),
_bG/* countries718 */ = new T2(0,_bF/* Countries.countries720 */,_bE/* Countries.countries719 */),
_bH/* countries716 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guinea-Bissau"));
}),
_bI/* countries717 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GW"));
}),
_bJ/* countries715 */ = new T2(0,_bI/* Countries.countries717 */,_bH/* Countries.countries716 */),
_bK/* countries713 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Guyana"));
}),
_bL/* countries714 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GY"));
}),
_bM/* countries712 */ = new T2(0,_bL/* Countries.countries714 */,_bK/* Countries.countries713 */),
_bN/* countries710 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haiti"));
}),
_bO/* countries711 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_bP/* countries709 */ = new T2(0,_bO/* Countries.countries711 */,_bN/* Countries.countries710 */),
_bQ/* countries707 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Heard Island and McDonald Islands"));
}),
_bR/* countries708 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HM"));
}),
_bS/* countries706 */ = new T2(0,_bR/* Countries.countries708 */,_bQ/* Countries.countries707 */),
_bT/* countries704 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Holy See (Vatican City State)"));
}),
_bU/* countries705 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VA"));
}),
_bV/* countries703 */ = new T2(0,_bU/* Countries.countries705 */,_bT/* Countries.countries704 */),
_bW/* countries251 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zimbabwe"));
}),
_bX/* countries252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZW"));
}),
_bY/* countries250 */ = new T2(0,_bX/* Countries.countries252 */,_bW/* Countries.countries251 */),
_bZ/* countries249 */ = new T2(1,_bY/* Countries.countries250 */,_I/* GHC.Types.[] */),
_c0/* countries254 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Zambia"));
}),
_c1/* countries255 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZM"));
}),
_c2/* countries253 */ = new T2(0,_c1/* Countries.countries255 */,_c0/* Countries.countries254 */),
_c3/* countries248 */ = new T2(1,_c2/* Countries.countries253 */,_bZ/* Countries.countries249 */),
_c4/* countries257 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yemen"));
}),
_c5/* countries258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YE"));
}),
_c6/* countries256 */ = new T2(0,_c5/* Countries.countries258 */,_c4/* Countries.countries257 */),
_c7/* countries247 */ = new T2(1,_c6/* Countries.countries256 */,_c3/* Countries.countries248 */),
_c8/* countries260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Western Sahara"));
}),
_c9/* countries261 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EH"));
}),
_ca/* countries259 */ = new T2(0,_c9/* Countries.countries261 */,_c8/* Countries.countries260 */),
_cb/* countries246 */ = new T2(1,_ca/* Countries.countries259 */,_c7/* Countries.countries247 */),
_cc/* countries263 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Wallis and Futuna"));
}),
_cd/* countries264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WF"));
}),
_ce/* countries262 */ = new T2(0,_cd/* Countries.countries264 */,_cc/* Countries.countries263 */),
_cf/* countries245 */ = new T2(1,_ce/* Countries.countries262 */,_cb/* Countries.countries246 */),
_cg/* countries266 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, U.S."));
}),
_ch/* countries267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VI"));
}),
_ci/* countries265 */ = new T2(0,_ch/* Countries.countries267 */,_cg/* Countries.countries266 */),
_cj/* countries244 */ = new T2(1,_ci/* Countries.countries265 */,_cf/* Countries.countries245 */),
_ck/* countries269 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Virgin Islands, British"));
}),
_cl/* countries270 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VG"));
}),
_cm/* countries268 */ = new T2(0,_cl/* Countries.countries270 */,_ck/* Countries.countries269 */),
_cn/* countries243 */ = new T2(1,_cm/* Countries.countries268 */,_cj/* Countries.countries244 */),
_co/* countries272 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Viet Nam"));
}),
_cp/* countries273 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VN"));
}),
_cq/* countries271 */ = new T2(0,_cp/* Countries.countries273 */,_co/* Countries.countries272 */),
_cr/* countries242 */ = new T2(1,_cq/* Countries.countries271 */,_cn/* Countries.countries243 */),
_cs/* countries275 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Venezuela, Bolivarian Republic of"));
}),
_ct/* countries276 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VE"));
}),
_cu/* countries274 */ = new T2(0,_ct/* Countries.countries276 */,_cs/* Countries.countries275 */),
_cv/* countries241 */ = new T2(1,_cu/* Countries.countries274 */,_cr/* Countries.countries242 */),
_cw/* countries278 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Vanuatu"));
}),
_cx/* countries279 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VU"));
}),
_cy/* countries277 */ = new T2(0,_cx/* Countries.countries279 */,_cw/* Countries.countries278 */),
_cz/* countries240 */ = new T2(1,_cy/* Countries.countries277 */,_cv/* Countries.countries241 */),
_cA/* countries281 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uzbekistan"));
}),
_cB/* countries282 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UZ"));
}),
_cC/* countries280 */ = new T2(0,_cB/* Countries.countries282 */,_cA/* Countries.countries281 */),
_cD/* countries239 */ = new T2(1,_cC/* Countries.countries280 */,_cz/* Countries.countries240 */),
_cE/* countries284 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uruguay"));
}),
_cF/* countries285 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UY"));
}),
_cG/* countries283 */ = new T2(0,_cF/* Countries.countries285 */,_cE/* Countries.countries284 */),
_cH/* countries238 */ = new T2(1,_cG/* Countries.countries283 */,_cD/* Countries.countries239 */),
_cI/* countries287 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States Minor Outlying Islands"));
}),
_cJ/* countries288 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UM"));
}),
_cK/* countries286 */ = new T2(0,_cJ/* Countries.countries288 */,_cI/* Countries.countries287 */),
_cL/* countries237 */ = new T2(1,_cK/* Countries.countries286 */,_cH/* Countries.countries238 */),
_cM/* countries290 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United States"));
}),
_cN/* countries291 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_cO/* countries289 */ = new T2(0,_cN/* Countries.countries291 */,_cM/* Countries.countries290 */),
_cP/* countries236 */ = new T2(1,_cO/* Countries.countries289 */,_cL/* Countries.countries237 */),
_cQ/* countries293 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Kingdom"));
}),
_cR/* countries294 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_cS/* countries292 */ = new T2(0,_cR/* Countries.countries294 */,_cQ/* Countries.countries293 */),
_cT/* countries235 */ = new T2(1,_cS/* Countries.countries292 */,_cP/* Countries.countries236 */),
_cU/* countries296 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("United Arab Emirates"));
}),
_cV/* countries297 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AE"));
}),
_cW/* countries295 */ = new T2(0,_cV/* Countries.countries297 */,_cU/* Countries.countries296 */),
_cX/* countries234 */ = new T2(1,_cW/* Countries.countries295 */,_cT/* Countries.countries235 */),
_cY/* countries299 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ukraine"));
}),
_cZ/* countries300 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UA"));
}),
_d0/* countries298 */ = new T2(0,_cZ/* Countries.countries300 */,_cY/* Countries.countries299 */),
_d1/* countries233 */ = new T2(1,_d0/* Countries.countries298 */,_cX/* Countries.countries234 */),
_d2/* countries302 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Uganda"));
}),
_d3/* countries303 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("UG"));
}),
_d4/* countries301 */ = new T2(0,_d3/* Countries.countries303 */,_d2/* Countries.countries302 */),
_d5/* countries232 */ = new T2(1,_d4/* Countries.countries301 */,_d1/* Countries.countries233 */),
_d6/* countries305 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tuvalu"));
}),
_d7/* countries306 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TV"));
}),
_d8/* countries304 */ = new T2(0,_d7/* Countries.countries306 */,_d6/* Countries.countries305 */),
_d9/* countries231 */ = new T2(1,_d8/* Countries.countries304 */,_d5/* Countries.countries232 */),
_da/* countries308 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turks and Caicos Islands"));
}),
_db/* countries309 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TC"));
}),
_dc/* countries307 */ = new T2(0,_db/* Countries.countries309 */,_da/* Countries.countries308 */),
_dd/* countries230 */ = new T2(1,_dc/* Countries.countries307 */,_d9/* Countries.countries231 */),
_de/* countries311 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkmenistan"));
}),
_df/* countries312 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TM"));
}),
_dg/* countries310 */ = new T2(0,_df/* Countries.countries312 */,_de/* Countries.countries311 */),
_dh/* countries229 */ = new T2(1,_dg/* Countries.countries310 */,_dd/* Countries.countries230 */),
_di/* countries314 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Turkey"));
}),
_dj/* countries315 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TR"));
}),
_dk/* countries313 */ = new T2(0,_dj/* Countries.countries315 */,_di/* Countries.countries314 */),
_dl/* countries228 */ = new T2(1,_dk/* Countries.countries313 */,_dh/* Countries.countries229 */),
_dm/* countries317 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tunisia"));
}),
_dn/* countries318 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TN"));
}),
_do/* countries316 */ = new T2(0,_dn/* Countries.countries318 */,_dm/* Countries.countries317 */),
_dp/* countries227 */ = new T2(1,_do/* Countries.countries316 */,_dl/* Countries.countries228 */),
_dq/* countries320 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Trinidad and Tobago"));
}),
_dr/* countries321 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TT"));
}),
_ds/* countries319 */ = new T2(0,_dr/* Countries.countries321 */,_dq/* Countries.countries320 */),
_dt/* countries226 */ = new T2(1,_ds/* Countries.countries319 */,_dp/* Countries.countries227 */),
_du/* countries323 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tonga"));
}),
_dv/* countries324 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TO"));
}),
_dw/* countries322 */ = new T2(0,_dv/* Countries.countries324 */,_du/* Countries.countries323 */),
_dx/* countries225 */ = new T2(1,_dw/* Countries.countries322 */,_dt/* Countries.countries226 */),
_dy/* countries326 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tokelau"));
}),
_dz/* countries327 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TK"));
}),
_dA/* countries325 */ = new T2(0,_dz/* Countries.countries327 */,_dy/* Countries.countries326 */),
_dB/* countries224 */ = new T2(1,_dA/* Countries.countries325 */,_dx/* Countries.countries225 */),
_dC/* countries329 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Togo"));
}),
_dD/* countries330 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TG"));
}),
_dE/* countries328 */ = new T2(0,_dD/* Countries.countries330 */,_dC/* Countries.countries329 */),
_dF/* countries223 */ = new T2(1,_dE/* Countries.countries328 */,_dB/* Countries.countries224 */),
_dG/* countries332 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Timor-Leste"));
}),
_dH/* countries333 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TL"));
}),
_dI/* countries331 */ = new T2(0,_dH/* Countries.countries333 */,_dG/* Countries.countries332 */),
_dJ/* countries222 */ = new T2(1,_dI/* Countries.countries331 */,_dF/* Countries.countries223 */),
_dK/* countries335 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Thailand"));
}),
_dL/* countries336 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TH"));
}),
_dM/* countries334 */ = new T2(0,_dL/* Countries.countries336 */,_dK/* Countries.countries335 */),
_dN/* countries221 */ = new T2(1,_dM/* Countries.countries334 */,_dJ/* Countries.countries222 */),
_dO/* countries338 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tanzania, United Republic of"));
}),
_dP/* countries339 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TZ"));
}),
_dQ/* countries337 */ = new T2(0,_dP/* Countries.countries339 */,_dO/* Countries.countries338 */),
_dR/* countries220 */ = new T2(1,_dQ/* Countries.countries337 */,_dN/* Countries.countries221 */),
_dS/* countries341 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Tajikistan"));
}),
_dT/* countries342 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TJ"));
}),
_dU/* countries340 */ = new T2(0,_dT/* Countries.countries342 */,_dS/* Countries.countries341 */),
_dV/* countries219 */ = new T2(1,_dU/* Countries.countries340 */,_dR/* Countries.countries220 */),
_dW/* countries344 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Taiwan, Province of China"));
}),
_dX/* countries345 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TW"));
}),
_dY/* countries343 */ = new T2(0,_dX/* Countries.countries345 */,_dW/* Countries.countries344 */),
_dZ/* countries218 */ = new T2(1,_dY/* Countries.countries343 */,_dV/* Countries.countries219 */),
_e0/* countries347 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Syrian Arab Republic"));
}),
_e1/* countries348 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SY"));
}),
_e2/* countries346 */ = new T2(0,_e1/* Countries.countries348 */,_e0/* Countries.countries347 */),
_e3/* countries217 */ = new T2(1,_e2/* Countries.countries346 */,_dZ/* Countries.countries218 */),
_e4/* countries350 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Switzerland"));
}),
_e5/* countries351 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CH"));
}),
_e6/* countries349 */ = new T2(0,_e5/* Countries.countries351 */,_e4/* Countries.countries350 */),
_e7/* countries216 */ = new T2(1,_e6/* Countries.countries349 */,_e3/* Countries.countries217 */),
_e8/* countries353 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sweden"));
}),
_e9/* countries354 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SE"));
}),
_ea/* countries352 */ = new T2(0,_e9/* Countries.countries354 */,_e8/* Countries.countries353 */),
_eb/* countries215 */ = new T2(1,_ea/* Countries.countries352 */,_e7/* Countries.countries216 */),
_ec/* countries356 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Swaziland"));
}),
_ed/* countries357 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SZ"));
}),
_ee/* countries355 */ = new T2(0,_ed/* Countries.countries357 */,_ec/* Countries.countries356 */),
_ef/* countries214 */ = new T2(1,_ee/* Countries.countries355 */,_eb/* Countries.countries215 */),
_eg/* countries359 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Svalbard and Jan Mayen"));
}),
_eh/* countries360 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SJ"));
}),
_ei/* countries358 */ = new T2(0,_eh/* Countries.countries360 */,_eg/* Countries.countries359 */),
_ej/* countries213 */ = new T2(1,_ei/* Countries.countries358 */,_ef/* Countries.countries214 */),
_ek/* countries362 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Suriname"));
}),
_el/* countries363 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SR"));
}),
_em/* countries361 */ = new T2(0,_el/* Countries.countries363 */,_ek/* Countries.countries362 */),
_en/* countries212 */ = new T2(1,_em/* Countries.countries361 */,_ej/* Countries.countries213 */),
_eo/* countries365 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sudan"));
}),
_ep/* countries366 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SD"));
}),
_eq/* countries364 */ = new T2(0,_ep/* Countries.countries366 */,_eo/* Countries.countries365 */),
_er/* countries211 */ = new T2(1,_eq/* Countries.countries364 */,_en/* Countries.countries212 */),
_es/* countries368 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sri Lanka"));
}),
_et/* countries369 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LK"));
}),
_eu/* countries367 */ = new T2(0,_et/* Countries.countries369 */,_es/* Countries.countries368 */),
_ev/* countries210 */ = new T2(1,_eu/* Countries.countries367 */,_er/* Countries.countries211 */),
_ew/* countries371 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Spain"));
}),
_ex/* countries372 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ES"));
}),
_ey/* countries370 */ = new T2(0,_ex/* Countries.countries372 */,_ew/* Countries.countries371 */),
_ez/* countries209 */ = new T2(1,_ey/* Countries.countries370 */,_ev/* Countries.countries210 */),
_eA/* countries374 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Sudan"));
}),
_eB/* countries375 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SS"));
}),
_eC/* countries373 */ = new T2(0,_eB/* Countries.countries375 */,_eA/* Countries.countries374 */),
_eD/* countries208 */ = new T2(1,_eC/* Countries.countries373 */,_ez/* Countries.countries209 */),
_eE/* countries377 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Georgia and the South Sandwich Islands"));
}),
_eF/* countries378 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_eG/* countries376 */ = new T2(0,_eF/* Countries.countries378 */,_eE/* Countries.countries377 */),
_eH/* countries207 */ = new T2(1,_eG/* Countries.countries376 */,_eD/* Countries.countries208 */),
_eI/* countries380 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("South Africa"));
}),
_eJ/* countries381 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ZA"));
}),
_eK/* countries379 */ = new T2(0,_eJ/* Countries.countries381 */,_eI/* Countries.countries380 */),
_eL/* countries206 */ = new T2(1,_eK/* Countries.countries379 */,_eH/* Countries.countries207 */),
_eM/* countries383 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Somalia"));
}),
_eN/* countries384 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_eO/* countries382 */ = new T2(0,_eN/* Countries.countries384 */,_eM/* Countries.countries383 */),
_eP/* countries205 */ = new T2(1,_eO/* Countries.countries382 */,_eL/* Countries.countries206 */),
_eQ/* countries386 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Solomon Islands"));
}),
_eR/* countries387 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SB"));
}),
_eS/* countries385 */ = new T2(0,_eR/* Countries.countries387 */,_eQ/* Countries.countries386 */),
_eT/* countries204 */ = new T2(1,_eS/* Countries.countries385 */,_eP/* Countries.countries205 */),
_eU/* countries389 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovenia"));
}),
_eV/* countries390 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_eW/* countries388 */ = new T2(0,_eV/* Countries.countries390 */,_eU/* Countries.countries389 */),
_eX/* countries203 */ = new T2(1,_eW/* Countries.countries388 */,_eT/* Countries.countries204 */),
_eY/* countries392 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Slovakia"));
}),
_eZ/* countries393 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SK"));
}),
_f0/* countries391 */ = new T2(0,_eZ/* Countries.countries393 */,_eY/* Countries.countries392 */),
_f1/* countries202 */ = new T2(1,_f0/* Countries.countries391 */,_eX/* Countries.countries203 */),
_f2/* countries395 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sint Maarten (Dutch part)"));
}),
_f3/* countries396 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SX"));
}),
_f4/* countries394 */ = new T2(0,_f3/* Countries.countries396 */,_f2/* Countries.countries395 */),
_f5/* countries201 */ = new T2(1,_f4/* Countries.countries394 */,_f1/* Countries.countries202 */),
_f6/* countries398 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Singapore"));
}),
_f7/* countries399 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SG"));
}),
_f8/* countries397 */ = new T2(0,_f7/* Countries.countries399 */,_f6/* Countries.countries398 */),
_f9/* countries200 */ = new T2(1,_f8/* Countries.countries397 */,_f5/* Countries.countries201 */),
_fa/* countries401 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sierra Leone"));
}),
_fb/* countries402 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SL"));
}),
_fc/* countries400 */ = new T2(0,_fb/* Countries.countries402 */,_fa/* Countries.countries401 */),
_fd/* countries199 */ = new T2(1,_fc/* Countries.countries400 */,_f9/* Countries.countries200 */),
_fe/* countries404 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Seychelles"));
}),
_ff/* countries405 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SC"));
}),
_fg/* countries403 */ = new T2(0,_ff/* Countries.countries405 */,_fe/* Countries.countries404 */),
_fh/* countries198 */ = new T2(1,_fg/* Countries.countries403 */,_fd/* Countries.countries199 */),
_fi/* countries407 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Serbia"));
}),
_fj/* countries408 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_fk/* countries406 */ = new T2(0,_fj/* Countries.countries408 */,_fi/* Countries.countries407 */),
_fl/* countries197 */ = new T2(1,_fk/* Countries.countries406 */,_fh/* Countries.countries198 */),
_fm/* countries410 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Senegal"));
}),
_fn/* countries411 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SN"));
}),
_fo/* countries409 */ = new T2(0,_fn/* Countries.countries411 */,_fm/* Countries.countries410 */),
_fp/* countries196 */ = new T2(1,_fo/* Countries.countries409 */,_fl/* Countries.countries197 */),
_fq/* countries413 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saudi Arabia"));
}),
_fr/* countries414 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SA"));
}),
_fs/* countries412 */ = new T2(0,_fr/* Countries.countries414 */,_fq/* Countries.countries413 */),
_ft/* countries195 */ = new T2(1,_fs/* Countries.countries412 */,_fp/* Countries.countries196 */),
_fu/* countries416 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sao Tome and Principe"));
}),
_fv/* countries417 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ST"));
}),
_fw/* countries415 */ = new T2(0,_fv/* Countries.countries417 */,_fu/* Countries.countries416 */),
_fx/* countries194 */ = new T2(1,_fw/* Countries.countries415 */,_ft/* Countries.countries195 */),
_fy/* countries419 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("San Marino"));
}),
_fz/* countries420 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SM"));
}),
_fA/* countries418 */ = new T2(0,_fz/* Countries.countries420 */,_fy/* Countries.countries419 */),
_fB/* countries193 */ = new T2(1,_fA/* Countries.countries418 */,_fx/* Countries.countries194 */),
_fC/* countries422 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Samoa"));
}),
_fD/* countries423 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("WS"));
}),
_fE/* countries421 */ = new T2(0,_fD/* Countries.countries423 */,_fC/* Countries.countries422 */),
_fF/* countries192 */ = new T2(1,_fE/* Countries.countries421 */,_fB/* Countries.countries193 */),
_fG/* countries425 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Vincent and the Grenadines"));
}),
_fH/* countries426 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VC"));
}),
_fI/* countries424 */ = new T2(0,_fH/* Countries.countries426 */,_fG/* Countries.countries425 */),
_fJ/* countries191 */ = new T2(1,_fI/* Countries.countries424 */,_fF/* Countries.countries192 */),
_fK/* countries428 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Pierre and Miquelon"));
}),
_fL/* countries429 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PM"));
}),
_fM/* countries427 */ = new T2(0,_fL/* Countries.countries429 */,_fK/* Countries.countries428 */),
_fN/* countries190 */ = new T2(1,_fM/* Countries.countries427 */,_fJ/* Countries.countries191 */),
_fO/* countries431 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Martin (French part)"));
}),
_fP/* countries432 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MF"));
}),
_fQ/* countries430 */ = new T2(0,_fP/* Countries.countries432 */,_fO/* Countries.countries431 */),
_fR/* countries189 */ = new T2(1,_fQ/* Countries.countries430 */,_fN/* Countries.countries190 */),
_fS/* countries434 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Lucia"));
}),
_fT/* countries435 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LC"));
}),
_fU/* countries433 */ = new T2(0,_fT/* Countries.countries435 */,_fS/* Countries.countries434 */),
_fV/* countries188 */ = new T2(1,_fU/* Countries.countries433 */,_fR/* Countries.countries189 */),
_fW/* countries437 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Kitts and Nevis"));
}),
_fX/* countries438 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KN"));
}),
_fY/* countries436 */ = new T2(0,_fX/* Countries.countries438 */,_fW/* Countries.countries437 */),
_fZ/* countries187 */ = new T2(1,_fY/* Countries.countries436 */,_fV/* Countries.countries188 */),
_g0/* countries440 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Helena, Ascension and Tristan da Cunha"));
}),
_g1/* countries441 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SH"));
}),
_g2/* countries439 */ = new T2(0,_g1/* Countries.countries441 */,_g0/* Countries.countries440 */),
_g3/* countries186 */ = new T2(1,_g2/* Countries.countries439 */,_fZ/* Countries.countries187 */),
_g4/* countries443 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Saint Barth\u00e9lemy"));
}),
_g5/* countries444 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BL"));
}),
_g6/* countries442 */ = new T2(0,_g5/* Countries.countries444 */,_g4/* Countries.countries443 */),
_g7/* countries185 */ = new T2(1,_g6/* Countries.countries442 */,_g3/* Countries.countries186 */),
_g8/* countries446 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rwanda"));
}),
_g9/* countries447 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RW"));
}),
_ga/* countries445 */ = new T2(0,_g9/* Countries.countries447 */,_g8/* Countries.countries446 */),
_gb/* countries184 */ = new T2(1,_ga/* Countries.countries445 */,_g7/* Countries.countries185 */),
_gc/* countries449 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Russian Federation"));
}),
_gd/* countries450 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RU"));
}),
_ge/* countries448 */ = new T2(0,_gd/* Countries.countries450 */,_gc/* Countries.countries449 */),
_gf/* countries183 */ = new T2(1,_ge/* Countries.countries448 */,_gb/* Countries.countries184 */),
_gg/* countries452 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Romania"));
}),
_gh/* countries453 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RO"));
}),
_gi/* countries451 */ = new T2(0,_gh/* Countries.countries453 */,_gg/* Countries.countries452 */),
_gj/* countries182 */ = new T2(1,_gi/* Countries.countries451 */,_gf/* Countries.countries183 */),
_gk/* countries455 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("R\u00e9union"));
}),
_gl/* countries456 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RE"));
}),
_gm/* countries454 */ = new T2(0,_gl/* Countries.countries456 */,_gk/* Countries.countries455 */),
_gn/* countries181 */ = new T2(1,_gm/* Countries.countries454 */,_gj/* Countries.countries182 */),
_go/* countries458 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Qatar"));
}),
_gp/* countries459 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("QA"));
}),
_gq/* countries457 */ = new T2(0,_gp/* Countries.countries459 */,_go/* Countries.countries458 */),
_gr/* countries180 */ = new T2(1,_gq/* Countries.countries457 */,_gn/* Countries.countries181 */),
_gs/* countries461 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Puerto Rico"));
}),
_gt/* countries462 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PR"));
}),
_gu/* countries460 */ = new T2(0,_gt/* Countries.countries462 */,_gs/* Countries.countries461 */),
_gv/* countries179 */ = new T2(1,_gu/* Countries.countries460 */,_gr/* Countries.countries180 */),
_gw/* countries464 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Portugal"));
}),
_gx/* countries465 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PT"));
}),
_gy/* countries463 */ = new T2(0,_gx/* Countries.countries465 */,_gw/* Countries.countries464 */),
_gz/* countries178 */ = new T2(1,_gy/* Countries.countries463 */,_gv/* Countries.countries179 */),
_gA/* countries467 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Poland"));
}),
_gB/* countries468 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PL"));
}),
_gC/* countries466 */ = new T2(0,_gB/* Countries.countries468 */,_gA/* Countries.countries467 */),
_gD/* countries177 */ = new T2(1,_gC/* Countries.countries466 */,_gz/* Countries.countries178 */),
_gE/* countries470 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pitcairn"));
}),
_gF/* countries471 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PN"));
}),
_gG/* countries469 */ = new T2(0,_gF/* Countries.countries471 */,_gE/* Countries.countries470 */),
_gH/* countries176 */ = new T2(1,_gG/* Countries.countries469 */,_gD/* Countries.countries177 */),
_gI/* countries473 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Philippines"));
}),
_gJ/* countries474 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PH"));
}),
_gK/* countries472 */ = new T2(0,_gJ/* Countries.countries474 */,_gI/* Countries.countries473 */),
_gL/* countries175 */ = new T2(1,_gK/* Countries.countries472 */,_gH/* Countries.countries176 */),
_gM/* countries476 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Peru"));
}),
_gN/* countries477 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PE"));
}),
_gO/* countries475 */ = new T2(0,_gN/* Countries.countries477 */,_gM/* Countries.countries476 */),
_gP/* countries174 */ = new T2(1,_gO/* Countries.countries475 */,_gL/* Countries.countries175 */),
_gQ/* countries479 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Paraguay"));
}),
_gR/* countries480 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PY"));
}),
_gS/* countries478 */ = new T2(0,_gR/* Countries.countries480 */,_gQ/* Countries.countries479 */),
_gT/* countries173 */ = new T2(1,_gS/* Countries.countries478 */,_gP/* Countries.countries174 */),
_gU/* countries482 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Papua New Guinea"));
}),
_gV/* countries483 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PG"));
}),
_gW/* countries481 */ = new T2(0,_gV/* Countries.countries483 */,_gU/* Countries.countries482 */),
_gX/* countries172 */ = new T2(1,_gW/* Countries.countries481 */,_gT/* Countries.countries173 */),
_gY/* countries485 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Panama"));
}),
_gZ/* countries486 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PA"));
}),
_h0/* countries484 */ = new T2(0,_gZ/* Countries.countries486 */,_gY/* Countries.countries485 */),
_h1/* countries171 */ = new T2(1,_h0/* Countries.countries484 */,_gX/* Countries.countries172 */),
_h2/* countries488 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palestinian Territory, Occupied"));
}),
_h3/* countries489 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PS"));
}),
_h4/* countries487 */ = new T2(0,_h3/* Countries.countries489 */,_h2/* Countries.countries488 */),
_h5/* countries170 */ = new T2(1,_h4/* Countries.countries487 */,_h1/* Countries.countries171 */),
_h6/* countries491 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Palau"));
}),
_h7/* countries492 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PW"));
}),
_h8/* countries490 */ = new T2(0,_h7/* Countries.countries492 */,_h6/* Countries.countries491 */),
_h9/* countries169 */ = new T2(1,_h8/* Countries.countries490 */,_h5/* Countries.countries170 */),
_ha/* countries494 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Pakistan"));
}),
_hb/* countries495 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PK"));
}),
_hc/* countries493 */ = new T2(0,_hb/* Countries.countries495 */,_ha/* Countries.countries494 */),
_hd/* countries168 */ = new T2(1,_hc/* Countries.countries493 */,_h9/* Countries.countries169 */),
_he/* countries497 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Oman"));
}),
_hf/* countries498 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("OM"));
}),
_hg/* countries496 */ = new T2(0,_hf/* Countries.countries498 */,_he/* Countries.countries497 */),
_hh/* countries167 */ = new T2(1,_hg/* Countries.countries496 */,_hd/* Countries.countries168 */),
_hi/* countries500 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norway"));
}),
_hj/* countries501 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NO"));
}),
_hk/* countries499 */ = new T2(0,_hj/* Countries.countries501 */,_hi/* Countries.countries500 */),
_hl/* countries166 */ = new T2(1,_hk/* Countries.countries499 */,_hh/* Countries.countries167 */),
_hm/* countries503 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Northern Mariana Islands"));
}),
_hn/* countries504 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MP"));
}),
_ho/* countries502 */ = new T2(0,_hn/* Countries.countries504 */,_hm/* Countries.countries503 */),
_hp/* countries165 */ = new T2(1,_ho/* Countries.countries502 */,_hl/* Countries.countries166 */),
_hq/* countries506 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Norfolk Island"));
}),
_hr/* countries507 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NF"));
}),
_hs/* countries505 */ = new T2(0,_hr/* Countries.countries507 */,_hq/* Countries.countries506 */),
_ht/* countries164 */ = new T2(1,_hs/* Countries.countries505 */,_hp/* Countries.countries165 */),
_hu/* countries509 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niue"));
}),
_hv/* countries510 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NU"));
}),
_hw/* countries508 */ = new T2(0,_hv/* Countries.countries510 */,_hu/* Countries.countries509 */),
_hx/* countries163 */ = new T2(1,_hw/* Countries.countries508 */,_ht/* Countries.countries164 */),
_hy/* countries512 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nigeria"));
}),
_hz/* countries513 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NG"));
}),
_hA/* countries511 */ = new T2(0,_hz/* Countries.countries513 */,_hy/* Countries.countries512 */),
_hB/* countries162 */ = new T2(1,_hA/* Countries.countries511 */,_hx/* Countries.countries163 */),
_hC/* countries515 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Niger"));
}),
_hD/* countries516 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NE"));
}),
_hE/* countries514 */ = new T2(0,_hD/* Countries.countries516 */,_hC/* Countries.countries515 */),
_hF/* countries161 */ = new T2(1,_hE/* Countries.countries514 */,_hB/* Countries.countries162 */),
_hG/* countries518 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nicaragua"));
}),
_hH/* countries519 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NI"));
}),
_hI/* countries517 */ = new T2(0,_hH/* Countries.countries519 */,_hG/* Countries.countries518 */),
_hJ/* countries160 */ = new T2(1,_hI/* Countries.countries517 */,_hF/* Countries.countries161 */),
_hK/* countries521 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Zealand"));
}),
_hL/* countries522 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NZ"));
}),
_hM/* countries520 */ = new T2(0,_hL/* Countries.countries522 */,_hK/* Countries.countries521 */),
_hN/* countries159 */ = new T2(1,_hM/* Countries.countries520 */,_hJ/* Countries.countries160 */),
_hO/* countries524 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("New Caledonia"));
}),
_hP/* countries525 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NC"));
}),
_hQ/* countries523 */ = new T2(0,_hP/* Countries.countries525 */,_hO/* Countries.countries524 */),
_hR/* countries158 */ = new T2(1,_hQ/* Countries.countries523 */,_hN/* Countries.countries159 */),
_hS/* countries527 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Netherlands"));
}),
_hT/* countries528 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NL"));
}),
_hU/* countries526 */ = new T2(0,_hT/* Countries.countries528 */,_hS/* Countries.countries527 */),
_hV/* countries157 */ = new T2(1,_hU/* Countries.countries526 */,_hR/* Countries.countries158 */),
_hW/* countries530 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nepal"));
}),
_hX/* countries531 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NP"));
}),
_hY/* countries529 */ = new T2(0,_hX/* Countries.countries531 */,_hW/* Countries.countries530 */),
_hZ/* countries156 */ = new T2(1,_hY/* Countries.countries529 */,_hV/* Countries.countries157 */),
_i0/* countries533 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Nauru"));
}),
_i1/* countries534 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NR"));
}),
_i2/* countries532 */ = new T2(0,_i1/* Countries.countries534 */,_i0/* Countries.countries533 */),
_i3/* countries155 */ = new T2(1,_i2/* Countries.countries532 */,_hZ/* Countries.countries156 */),
_i4/* countries536 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Namibia"));
}),
_i5/* countries537 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NA"));
}),
_i6/* countries535 */ = new T2(0,_i5/* Countries.countries537 */,_i4/* Countries.countries536 */),
_i7/* countries154 */ = new T2(1,_i6/* Countries.countries535 */,_i3/* Countries.countries155 */),
_i8/* countries539 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Myanmar"));
}),
_i9/* countries540 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MM"));
}),
_ia/* countries538 */ = new T2(0,_i9/* Countries.countries540 */,_i8/* Countries.countries539 */),
_ib/* countries153 */ = new T2(1,_ia/* Countries.countries538 */,_i7/* Countries.countries154 */),
_ic/* countries542 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mozambique"));
}),
_id/* countries543 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MZ"));
}),
_ie/* countries541 */ = new T2(0,_id/* Countries.countries543 */,_ic/* Countries.countries542 */),
_if/* countries152 */ = new T2(1,_ie/* Countries.countries541 */,_ib/* Countries.countries153 */),
_ig/* countries545 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Morocco"));
}),
_ih/* countries546 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MA"));
}),
_ii/* countries544 */ = new T2(0,_ih/* Countries.countries546 */,_ig/* Countries.countries545 */),
_ij/* countries151 */ = new T2(1,_ii/* Countries.countries544 */,_if/* Countries.countries152 */),
_ik/* countries548 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montserrat"));
}),
_il/* countries549 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MS"));
}),
_im/* countries547 */ = new T2(0,_il/* Countries.countries549 */,_ik/* Countries.countries548 */),
_in/* countries150 */ = new T2(1,_im/* Countries.countries547 */,_ij/* Countries.countries151 */),
_io/* countries551 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Montenegro"));
}),
_ip/* countries552 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ME"));
}),
_iq/* countries550 */ = new T2(0,_ip/* Countries.countries552 */,_io/* Countries.countries551 */),
_ir/* countries149 */ = new T2(1,_iq/* Countries.countries550 */,_in/* Countries.countries150 */),
_is/* countries554 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mongolia"));
}),
_it/* countries555 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MN"));
}),
_iu/* countries553 */ = new T2(0,_it/* Countries.countries555 */,_is/* Countries.countries554 */),
_iv/* countries148 */ = new T2(1,_iu/* Countries.countries553 */,_ir/* Countries.countries149 */),
_iw/* countries557 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Monaco"));
}),
_ix/* countries558 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MC"));
}),
_iy/* countries556 */ = new T2(0,_ix/* Countries.countries558 */,_iw/* Countries.countries557 */),
_iz/* countries147 */ = new T2(1,_iy/* Countries.countries556 */,_iv/* Countries.countries148 */),
_iA/* countries560 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Moldova, Republic of"));
}),
_iB/* countries561 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MD"));
}),
_iC/* countries559 */ = new T2(0,_iB/* Countries.countries561 */,_iA/* Countries.countries560 */),
_iD/* countries146 */ = new T2(1,_iC/* Countries.countries559 */,_iz/* Countries.countries147 */),
_iE/* countries563 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Micronesia, Federated States of"));
}),
_iF/* countries564 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FM"));
}),
_iG/* countries562 */ = new T2(0,_iF/* Countries.countries564 */,_iE/* Countries.countries563 */),
_iH/* countries145 */ = new T2(1,_iG/* Countries.countries562 */,_iD/* Countries.countries146 */),
_iI/* countries566 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mexico"));
}),
_iJ/* countries567 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MX"));
}),
_iK/* countries565 */ = new T2(0,_iJ/* Countries.countries567 */,_iI/* Countries.countries566 */),
_iL/* countries144 */ = new T2(1,_iK/* Countries.countries565 */,_iH/* Countries.countries145 */),
_iM/* countries569 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mayotte"));
}),
_iN/* countries570 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("YT"));
}),
_iO/* countries568 */ = new T2(0,_iN/* Countries.countries570 */,_iM/* Countries.countries569 */),
_iP/* countries143 */ = new T2(1,_iO/* Countries.countries568 */,_iL/* Countries.countries144 */),
_iQ/* countries572 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritius"));
}),
_iR/* countries573 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MU"));
}),
_iS/* countries571 */ = new T2(0,_iR/* Countries.countries573 */,_iQ/* Countries.countries572 */),
_iT/* countries142 */ = new T2(1,_iS/* Countries.countries571 */,_iP/* Countries.countries143 */),
_iU/* countries575 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mauritania"));
}),
_iV/* countries576 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MR"));
}),
_iW/* countries574 */ = new T2(0,_iV/* Countries.countries576 */,_iU/* Countries.countries575 */),
_iX/* countries141 */ = new T2(1,_iW/* Countries.countries574 */,_iT/* Countries.countries142 */),
_iY/* countries578 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Martinique"));
}),
_iZ/* countries579 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MQ"));
}),
_j0/* countries577 */ = new T2(0,_iZ/* Countries.countries579 */,_iY/* Countries.countries578 */),
_j1/* countries140 */ = new T2(1,_j0/* Countries.countries577 */,_iX/* Countries.countries141 */),
_j2/* countries581 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Marshall Islands"));
}),
_j3/* countries582 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MH"));
}),
_j4/* countries580 */ = new T2(0,_j3/* Countries.countries582 */,_j2/* Countries.countries581 */),
_j5/* countries139 */ = new T2(1,_j4/* Countries.countries580 */,_j1/* Countries.countries140 */),
_j6/* countries584 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malta"));
}),
_j7/* countries585 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MT"));
}),
_j8/* countries583 */ = new T2(0,_j7/* Countries.countries585 */,_j6/* Countries.countries584 */),
_j9/* countries138 */ = new T2(1,_j8/* Countries.countries583 */,_j5/* Countries.countries139 */),
_ja/* countries587 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Mali"));
}),
_jb/* countries588 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ML"));
}),
_jc/* countries586 */ = new T2(0,_jb/* Countries.countries588 */,_ja/* Countries.countries587 */),
_jd/* countries137 */ = new T2(1,_jc/* Countries.countries586 */,_j9/* Countries.countries138 */),
_je/* countries590 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maldives"));
}),
_jf/* countries591 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MV"));
}),
_jg/* countries589 */ = new T2(0,_jf/* Countries.countries591 */,_je/* Countries.countries590 */),
_jh/* countries136 */ = new T2(1,_jg/* Countries.countries589 */,_jd/* Countries.countries137 */),
_ji/* countries593 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malaysia"));
}),
_jj/* countries594 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MY"));
}),
_jk/* countries592 */ = new T2(0,_jj/* Countries.countries594 */,_ji/* Countries.countries593 */),
_jl/* countries135 */ = new T2(1,_jk/* Countries.countries592 */,_jh/* Countries.countries136 */),
_jm/* countries596 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Malawi"));
}),
_jn/* countries597 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MW"));
}),
_jo/* countries595 */ = new T2(0,_jn/* Countries.countries597 */,_jm/* Countries.countries596 */),
_jp/* countries134 */ = new T2(1,_jo/* Countries.countries595 */,_jl/* Countries.countries135 */),
_jq/* countries599 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Madagascar"));
}),
_jr/* countries600 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MG"));
}),
_js/* countries598 */ = new T2(0,_jr/* Countries.countries600 */,_jq/* Countries.countries599 */),
_jt/* countries133 */ = new T2(1,_js/* Countries.countries598 */,_jp/* Countries.countries134 */),
_ju/* countries602 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macedonia, the former Yugoslav Republic of"));
}),
_jv/* countries603 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MK"));
}),
_jw/* countries601 */ = new T2(0,_jv/* Countries.countries603 */,_ju/* Countries.countries602 */),
_jx/* countries132 */ = new T2(1,_jw/* Countries.countries601 */,_jt/* Countries.countries133 */),
_jy/* countries605 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Macao"));
}),
_jz/* countries606 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MO"));
}),
_jA/* countries604 */ = new T2(0,_jz/* Countries.countries606 */,_jy/* Countries.countries605 */),
_jB/* countries131 */ = new T2(1,_jA/* Countries.countries604 */,_jx/* Countries.countries132 */),
_jC/* countries608 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Luxembourg"));
}),
_jD/* countries609 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LU"));
}),
_jE/* countries607 */ = new T2(0,_jD/* Countries.countries609 */,_jC/* Countries.countries608 */),
_jF/* countries130 */ = new T2(1,_jE/* Countries.countries607 */,_jB/* Countries.countries131 */),
_jG/* countries611 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lithuania"));
}),
_jH/* countries612 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LT"));
}),
_jI/* countries610 */ = new T2(0,_jH/* Countries.countries612 */,_jG/* Countries.countries611 */),
_jJ/* countries129 */ = new T2(1,_jI/* Countries.countries610 */,_jF/* Countries.countries130 */),
_jK/* countries614 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liechtenstein"));
}),
_jL/* countries615 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LI"));
}),
_jM/* countries613 */ = new T2(0,_jL/* Countries.countries615 */,_jK/* Countries.countries614 */),
_jN/* countries128 */ = new T2(1,_jM/* Countries.countries613 */,_jJ/* Countries.countries129 */),
_jO/* countries617 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Libya"));
}),
_jP/* countries618 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LY"));
}),
_jQ/* countries616 */ = new T2(0,_jP/* Countries.countries618 */,_jO/* Countries.countries617 */),
_jR/* countries127 */ = new T2(1,_jQ/* Countries.countries616 */,_jN/* Countries.countries128 */),
_jS/* countries620 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Liberia"));
}),
_jT/* countries621 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LR"));
}),
_jU/* countries619 */ = new T2(0,_jT/* Countries.countries621 */,_jS/* Countries.countries620 */),
_jV/* countries126 */ = new T2(1,_jU/* Countries.countries619 */,_jR/* Countries.countries127 */),
_jW/* countries623 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lesotho"));
}),
_jX/* countries624 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LS"));
}),
_jY/* countries622 */ = new T2(0,_jX/* Countries.countries624 */,_jW/* Countries.countries623 */),
_jZ/* countries125 */ = new T2(1,_jY/* Countries.countries622 */,_jV/* Countries.countries126 */),
_k0/* countries626 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lebanon"));
}),
_k1/* countries627 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LB"));
}),
_k2/* countries625 */ = new T2(0,_k1/* Countries.countries627 */,_k0/* Countries.countries626 */),
_k3/* countries124 */ = new T2(1,_k2/* Countries.countries625 */,_jZ/* Countries.countries125 */),
_k4/* countries629 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Latvia"));
}),
_k5/* countries630 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LV"));
}),
_k6/* countries628 */ = new T2(0,_k5/* Countries.countries630 */,_k4/* Countries.countries629 */),
_k7/* countries123 */ = new T2(1,_k6/* Countries.countries628 */,_k3/* Countries.countries124 */),
_k8/* countries632 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Lao People\'s Democratic Republic"));
}),
_k9/* countries633 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LA"));
}),
_ka/* countries631 */ = new T2(0,_k9/* Countries.countries633 */,_k8/* Countries.countries632 */),
_kb/* countries122 */ = new T2(1,_ka/* Countries.countries631 */,_k7/* Countries.countries123 */),
_kc/* countries635 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kyrgyzstan"));
}),
_kd/* countries636 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KG"));
}),
_ke/* countries634 */ = new T2(0,_kd/* Countries.countries636 */,_kc/* Countries.countries635 */),
_kf/* countries121 */ = new T2(1,_ke/* Countries.countries634 */,_kb/* Countries.countries122 */),
_kg/* countries638 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kuwait"));
}),
_kh/* countries639 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KW"));
}),
_ki/* countries637 */ = new T2(0,_kh/* Countries.countries639 */,_kg/* Countries.countries638 */),
_kj/* countries120 */ = new T2(1,_ki/* Countries.countries637 */,_kf/* Countries.countries121 */),
_kk/* countries641 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Republic of"));
}),
_kl/* countries642 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KR"));
}),
_km/* countries640 */ = new T2(0,_kl/* Countries.countries642 */,_kk/* Countries.countries641 */),
_kn/* countries119 */ = new T2(1,_km/* Countries.countries640 */,_kj/* Countries.countries120 */),
_ko/* countries644 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Korea, Democratic People\'s Republic of"));
}),
_kp/* countries645 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KP"));
}),
_kq/* countries643 */ = new T2(0,_kp/* Countries.countries645 */,_ko/* Countries.countries644 */),
_kr/* countries118 */ = new T2(1,_kq/* Countries.countries643 */,_kn/* Countries.countries119 */),
_ks/* countries647 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kiribati"));
}),
_kt/* countries648 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KI"));
}),
_ku/* countries646 */ = new T2(0,_kt/* Countries.countries648 */,_ks/* Countries.countries647 */),
_kv/* countries117 */ = new T2(1,_ku/* Countries.countries646 */,_kr/* Countries.countries118 */),
_kw/* countries650 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kenya"));
}),
_kx/* countries651 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KE"));
}),
_ky/* countries649 */ = new T2(0,_kx/* Countries.countries651 */,_kw/* Countries.countries650 */),
_kz/* countries116 */ = new T2(1,_ky/* Countries.countries649 */,_kv/* Countries.countries117 */),
_kA/* countries653 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Kazakhstan"));
}),
_kB/* countries654 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KZ"));
}),
_kC/* countries652 */ = new T2(0,_kB/* Countries.countries654 */,_kA/* Countries.countries653 */),
_kD/* countries115 */ = new T2(1,_kC/* Countries.countries652 */,_kz/* Countries.countries116 */),
_kE/* countries656 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jordan"));
}),
_kF/* countries657 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JO"));
}),
_kG/* countries655 */ = new T2(0,_kF/* Countries.countries657 */,_kE/* Countries.countries656 */),
_kH/* countries114 */ = new T2(1,_kG/* Countries.countries655 */,_kD/* Countries.countries115 */),
_kI/* countries659 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jersey"));
}),
_kJ/* countries660 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JE"));
}),
_kK/* countries658 */ = new T2(0,_kJ/* Countries.countries660 */,_kI/* Countries.countries659 */),
_kL/* countries113 */ = new T2(1,_kK/* Countries.countries658 */,_kH/* Countries.countries114 */),
_kM/* countries662 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Japan"));
}),
_kN/* countries663 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JP"));
}),
_kO/* countries661 */ = new T2(0,_kN/* Countries.countries663 */,_kM/* Countries.countries662 */),
_kP/* countries112 */ = new T2(1,_kO/* Countries.countries661 */,_kL/* Countries.countries113 */),
_kQ/* countries665 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Jamaica"));
}),
_kR/* countries666 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("JM"));
}),
_kS/* countries664 */ = new T2(0,_kR/* Countries.countries666 */,_kQ/* Countries.countries665 */),
_kT/* countries111 */ = new T2(1,_kS/* Countries.countries664 */,_kP/* Countries.countries112 */),
_kU/* countries668 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Italy"));
}),
_kV/* countries669 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IT"));
}),
_kW/* countries667 */ = new T2(0,_kV/* Countries.countries669 */,_kU/* Countries.countries668 */),
_kX/* countries110 */ = new T2(1,_kW/* Countries.countries667 */,_kT/* Countries.countries111 */),
_kY/* countries671 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Israel"));
}),
_kZ/* countries672 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IL"));
}),
_l0/* countries670 */ = new T2(0,_kZ/* Countries.countries672 */,_kY/* Countries.countries671 */),
_l1/* countries109 */ = new T2(1,_l0/* Countries.countries670 */,_kX/* Countries.countries110 */),
_l2/* countries674 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Isle of Man"));
}),
_l3/* countries675 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IM"));
}),
_l4/* countries673 */ = new T2(0,_l3/* Countries.countries675 */,_l2/* Countries.countries674 */),
_l5/* countries108 */ = new T2(1,_l4/* Countries.countries673 */,_l1/* Countries.countries109 */),
_l6/* countries677 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ireland"));
}),
_l7/* countries678 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IE"));
}),
_l8/* countries676 */ = new T2(0,_l7/* Countries.countries678 */,_l6/* Countries.countries677 */),
_l9/* countries107 */ = new T2(1,_l8/* Countries.countries676 */,_l5/* Countries.countries108 */),
_la/* countries680 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iraq"));
}),
_lb/* countries681 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IQ"));
}),
_lc/* countries679 */ = new T2(0,_lb/* Countries.countries681 */,_la/* Countries.countries680 */),
_ld/* countries106 */ = new T2(1,_lc/* Countries.countries679 */,_l9/* Countries.countries107 */),
_le/* countries683 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iran, Islamic Republic of"));
}),
_lf/* countries684 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IR"));
}),
_lg/* countries682 */ = new T2(0,_lf/* Countries.countries684 */,_le/* Countries.countries683 */),
_lh/* countries105 */ = new T2(1,_lg/* Countries.countries682 */,_ld/* Countries.countries106 */),
_li/* countries686 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Indonesia"));
}),
_lj/* countries687 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ID"));
}),
_lk/* countries685 */ = new T2(0,_lj/* Countries.countries687 */,_li/* Countries.countries686 */),
_ll/* countries104 */ = new T2(1,_lk/* Countries.countries685 */,_lh/* Countries.countries105 */),
_lm/* countries689 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("India"));
}),
_ln/* countries690 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IN"));
}),
_lo/* countries688 */ = new T2(0,_ln/* Countries.countries690 */,_lm/* Countries.countries689 */),
_lp/* countries103 */ = new T2(1,_lo/* Countries.countries688 */,_ll/* Countries.countries104 */),
_lq/* countries692 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Iceland"));
}),
_lr/* countries693 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IS"));
}),
_ls/* countries691 */ = new T2(0,_lr/* Countries.countries693 */,_lq/* Countries.countries692 */),
_lt/* countries102 */ = new T2(1,_ls/* Countries.countries691 */,_lp/* Countries.countries103 */),
_lu/* countries695 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hungary"));
}),
_lv/* countries696 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HU"));
}),
_lw/* countries694 */ = new T2(0,_lv/* Countries.countries696 */,_lu/* Countries.countries695 */),
_lx/* countries101 */ = new T2(1,_lw/* Countries.countries694 */,_lt/* Countries.countries102 */),
_ly/* countries698 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Hong Kong"));
}),
_lz/* countries699 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HK"));
}),
_lA/* countries697 */ = new T2(0,_lz/* Countries.countries699 */,_ly/* Countries.countries698 */),
_lB/* countries100 */ = new T2(1,_lA/* Countries.countries697 */,_lx/* Countries.countries101 */),
_lC/* countries701 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Honduras"));
}),
_lD/* countries702 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HN"));
}),
_lE/* countries700 */ = new T2(0,_lD/* Countries.countries702 */,_lC/* Countries.countries701 */),
_lF/* countries99 */ = new T2(1,_lE/* Countries.countries700 */,_lB/* Countries.countries100 */),
_lG/* countries98 */ = new T2(1,_bV/* Countries.countries703 */,_lF/* Countries.countries99 */),
_lH/* countries97 */ = new T2(1,_bS/* Countries.countries706 */,_lG/* Countries.countries98 */),
_lI/* countries96 */ = new T2(1,_bP/* Countries.countries709 */,_lH/* Countries.countries97 */),
_lJ/* countries95 */ = new T2(1,_bM/* Countries.countries712 */,_lI/* Countries.countries96 */),
_lK/* countries94 */ = new T2(1,_bJ/* Countries.countries715 */,_lJ/* Countries.countries95 */),
_lL/* countries93 */ = new T2(1,_bG/* Countries.countries718 */,_lK/* Countries.countries94 */),
_lM/* countries92 */ = new T2(1,_bD/* Countries.countries721 */,_lL/* Countries.countries93 */),
_lN/* countries91 */ = new T2(1,_bA/* Countries.countries724 */,_lM/* Countries.countries92 */),
_lO/* countries90 */ = new T2(1,_bx/* Countries.countries727 */,_lN/* Countries.countries91 */),
_lP/* countries89 */ = new T2(1,_bu/* Countries.countries730 */,_lO/* Countries.countries90 */),
_lQ/* countries88 */ = new T2(1,_br/* Countries.countries733 */,_lP/* Countries.countries89 */),
_lR/* countries87 */ = new T2(1,_bo/* Countries.countries736 */,_lQ/* Countries.countries88 */),
_lS/* countries86 */ = new T2(1,_bl/* Countries.countries739 */,_lR/* Countries.countries87 */),
_lT/* countries85 */ = new T2(1,_bi/* Countries.countries742 */,_lS/* Countries.countries86 */),
_lU/* countries84 */ = new T2(1,_bf/* Countries.countries745 */,_lT/* Countries.countries85 */),
_lV/* countries83 */ = new T2(1,_bc/* Countries.countries748 */,_lU/* Countries.countries84 */),
_lW/* countries82 */ = new T2(1,_b9/* Countries.countries751 */,_lV/* Countries.countries83 */),
_lX/* countries81 */ = new T2(1,_b6/* Countries.countries754 */,_lW/* Countries.countries82 */),
_lY/* countries80 */ = new T2(1,_b3/* Countries.countries757 */,_lX/* Countries.countries81 */),
_lZ/* countries79 */ = new T2(1,_b0/* Countries.countries760 */,_lY/* Countries.countries80 */),
_m0/* countries78 */ = new T2(1,_aX/* Countries.countries763 */,_lZ/* Countries.countries79 */),
_m1/* countries77 */ = new T2(1,_aU/* Countries.countries766 */,_m0/* Countries.countries78 */),
_m2/* countries76 */ = new T2(1,_aR/* Countries.countries769 */,_m1/* Countries.countries77 */),
_m3/* countries773 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finland"));
}),
_m4/* countries774 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FI"));
}),
_m5/* countries772 */ = new T2(0,_m4/* Countries.countries774 */,_m3/* Countries.countries773 */),
_m6/* countries75 */ = new T2(1,_m5/* Countries.countries772 */,_m2/* Countries.countries76 */),
_m7/* countries776 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Fiji"));
}),
_m8/* countries777 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FJ"));
}),
_m9/* countries775 */ = new T2(0,_m8/* Countries.countries777 */,_m7/* Countries.countries776 */),
_ma/* countries74 */ = new T2(1,_m9/* Countries.countries775 */,_m6/* Countries.countries75 */),
_mb/* countries779 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Faroe Islands"));
}),
_mc/* countries780 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FO"));
}),
_md/* countries778 */ = new T2(0,_mc/* Countries.countries780 */,_mb/* Countries.countries779 */),
_me/* countries73 */ = new T2(1,_md/* Countries.countries778 */,_ma/* Countries.countries74 */),
_mf/* countries782 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Falkland Islands (Malvinas)"));
}),
_mg/* countries783 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FK"));
}),
_mh/* countries781 */ = new T2(0,_mg/* Countries.countries783 */,_mf/* Countries.countries782 */),
_mi/* countries72 */ = new T2(1,_mh/* Countries.countries781 */,_me/* Countries.countries73 */),
_mj/* countries785 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ethiopia"));
}),
_mk/* countries786 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ET"));
}),
_ml/* countries784 */ = new T2(0,_mk/* Countries.countries786 */,_mj/* Countries.countries785 */),
_mm/* countries71 */ = new T2(1,_ml/* Countries.countries784 */,_mi/* Countries.countries72 */),
_mn/* countries788 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Estonia"));
}),
_mo/* countries789 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EE"));
}),
_mp/* countries787 */ = new T2(0,_mo/* Countries.countries789 */,_mn/* Countries.countries788 */),
_mq/* countries70 */ = new T2(1,_mp/* Countries.countries787 */,_mm/* Countries.countries71 */),
_mr/* countries791 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Eritrea"));
}),
_ms/* countries792 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ER"));
}),
_mt/* countries790 */ = new T2(0,_ms/* Countries.countries792 */,_mr/* Countries.countries791 */),
_mu/* countries69 */ = new T2(1,_mt/* Countries.countries790 */,_mq/* Countries.countries70 */),
_mv/* countries794 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Equatorial Guinea"));
}),
_mw/* countries795 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GQ"));
}),
_mx/* countries793 */ = new T2(0,_mw/* Countries.countries795 */,_mv/* Countries.countries794 */),
_my/* countries68 */ = new T2(1,_mx/* Countries.countries793 */,_mu/* Countries.countries69 */),
_mz/* countries797 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("El Salvador"));
}),
_mA/* countries798 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SV"));
}),
_mB/* countries796 */ = new T2(0,_mA/* Countries.countries798 */,_mz/* Countries.countries797 */),
_mC/* countries67 */ = new T2(1,_mB/* Countries.countries796 */,_my/* Countries.countries68 */),
_mD/* countries800 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Egypt"));
}),
_mE/* countries801 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EG"));
}),
_mF/* countries799 */ = new T2(0,_mE/* Countries.countries801 */,_mD/* Countries.countries800 */),
_mG/* countries66 */ = new T2(1,_mF/* Countries.countries799 */,_mC/* Countries.countries67 */),
_mH/* countries803 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Ecuador"));
}),
_mI/* countries804 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EC"));
}),
_mJ/* countries802 */ = new T2(0,_mI/* Countries.countries804 */,_mH/* Countries.countries803 */),
_mK/* countries65 */ = new T2(1,_mJ/* Countries.countries802 */,_mG/* Countries.countries66 */),
_mL/* countries806 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominican Republic"));
}),
_mM/* countries807 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DO"));
}),
_mN/* countries805 */ = new T2(0,_mM/* Countries.countries807 */,_mL/* Countries.countries806 */),
_mO/* countries64 */ = new T2(1,_mN/* Countries.countries805 */,_mK/* Countries.countries65 */),
_mP/* countries809 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Dominica"));
}),
_mQ/* countries810 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DM"));
}),
_mR/* countries808 */ = new T2(0,_mQ/* Countries.countries810 */,_mP/* Countries.countries809 */),
_mS/* countries63 */ = new T2(1,_mR/* Countries.countries808 */,_mO/* Countries.countries64 */),
_mT/* countries812 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Djibouti"));
}),
_mU/* countries813 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DJ"));
}),
_mV/* countries811 */ = new T2(0,_mU/* Countries.countries813 */,_mT/* Countries.countries812 */),
_mW/* countries62 */ = new T2(1,_mV/* Countries.countries811 */,_mS/* Countries.countries63 */),
_mX/* countries815 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Denmark"));
}),
_mY/* countries816 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DK"));
}),
_mZ/* countries814 */ = new T2(0,_mY/* Countries.countries816 */,_mX/* Countries.countries815 */),
_n0/* countries61 */ = new T2(1,_mZ/* Countries.countries814 */,_mW/* Countries.countries62 */),
_n1/* countries818 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Czech Republic"));
}),
_n2/* countries819 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CZ"));
}),
_n3/* countries817 */ = new T2(0,_n2/* Countries.countries819 */,_n1/* Countries.countries818 */),
_n4/* countries60 */ = new T2(1,_n3/* Countries.countries817 */,_n0/* Countries.countries61 */),
_n5/* countries821 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cyprus"));
}),
_n6/* countries822 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CY"));
}),
_n7/* countries820 */ = new T2(0,_n6/* Countries.countries822 */,_n5/* Countries.countries821 */),
_n8/* countries59 */ = new T2(1,_n7/* Countries.countries820 */,_n4/* Countries.countries60 */),
_n9/* countries824 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cura\u00e7ao"));
}),
_na/* countries825 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CW"));
}),
_nb/* countries823 */ = new T2(0,_na/* Countries.countries825 */,_n9/* Countries.countries824 */),
_nc/* countries58 */ = new T2(1,_nb/* Countries.countries823 */,_n8/* Countries.countries59 */),
_nd/* countries827 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cuba"));
}),
_ne/* countries828 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CU"));
}),
_nf/* countries826 */ = new T2(0,_ne/* Countries.countries828 */,_nd/* Countries.countries827 */),
_ng/* countries57 */ = new T2(1,_nf/* Countries.countries826 */,_nc/* Countries.countries58 */),
_nh/* countries830 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Croatia"));
}),
_ni/* countries831 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HR"));
}),
_nj/* countries829 */ = new T2(0,_ni/* Countries.countries831 */,_nh/* Countries.countries830 */),
_nk/* countries56 */ = new T2(1,_nj/* Countries.countries829 */,_ng/* Countries.countries57 */),
_nl/* countries833 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("C\u00f4te d\'Ivoire"));
}),
_nm/* countries834 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CI"));
}),
_nn/* countries832 */ = new T2(0,_nm/* Countries.countries834 */,_nl/* Countries.countries833 */),
_no/* countries55 */ = new T2(1,_nn/* Countries.countries832 */,_nk/* Countries.countries56 */),
_np/* countries836 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Costa Rica"));
}),
_nq/* countries837 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_nr/* countries835 */ = new T2(0,_nq/* Countries.countries837 */,_np/* Countries.countries836 */),
_ns/* countries54 */ = new T2(1,_nr/* Countries.countries835 */,_no/* Countries.countries55 */),
_nt/* countries839 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cook Islands"));
}),
_nu/* countries840 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CK"));
}),
_nv/* countries838 */ = new T2(0,_nu/* Countries.countries840 */,_nt/* Countries.countries839 */),
_nw/* countries53 */ = new T2(1,_nv/* Countries.countries838 */,_ns/* Countries.countries54 */),
_nx/* countries842 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo, the Democratic Republic of the"));
}),
_ny/* countries843 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CD"));
}),
_nz/* countries841 */ = new T2(0,_ny/* Countries.countries843 */,_nx/* Countries.countries842 */),
_nA/* countries52 */ = new T2(1,_nz/* Countries.countries841 */,_nw/* Countries.countries53 */),
_nB/* countries845 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Congo"));
}),
_nC/* countries846 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CG"));
}),
_nD/* countries844 */ = new T2(0,_nC/* Countries.countries846 */,_nB/* Countries.countries845 */),
_nE/* countries51 */ = new T2(1,_nD/* Countries.countries844 */,_nA/* Countries.countries52 */),
_nF/* countries848 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Comoros"));
}),
_nG/* countries849 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KM"));
}),
_nH/* countries847 */ = new T2(0,_nG/* Countries.countries849 */,_nF/* Countries.countries848 */),
_nI/* countries50 */ = new T2(1,_nH/* Countries.countries847 */,_nE/* Countries.countries51 */),
_nJ/* countries851 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Colombia"));
}),
_nK/* countries852 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CO"));
}),
_nL/* countries850 */ = new T2(0,_nK/* Countries.countries852 */,_nJ/* Countries.countries851 */),
_nM/* countries49 */ = new T2(1,_nL/* Countries.countries850 */,_nI/* Countries.countries50 */),
_nN/* countries854 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cocos (Keeling) Islands"));
}),
_nO/* countries855 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CC"));
}),
_nP/* countries853 */ = new T2(0,_nO/* Countries.countries855 */,_nN/* Countries.countries854 */),
_nQ/* countries48 */ = new T2(1,_nP/* Countries.countries853 */,_nM/* Countries.countries49 */),
_nR/* countries857 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Christmas Island"));
}),
_nS/* countries858 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CX"));
}),
_nT/* countries856 */ = new T2(0,_nS/* Countries.countries858 */,_nR/* Countries.countries857 */),
_nU/* countries47 */ = new T2(1,_nT/* Countries.countries856 */,_nQ/* Countries.countries48 */),
_nV/* countries860 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("China"));
}),
_nW/* countries861 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CN"));
}),
_nX/* countries859 */ = new T2(0,_nW/* Countries.countries861 */,_nV/* Countries.countries860 */),
_nY/* countries46 */ = new T2(1,_nX/* Countries.countries859 */,_nU/* Countries.countries47 */),
_nZ/* countries863 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chile"));
}),
_o0/* countries864 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CL"));
}),
_o1/* countries862 */ = new T2(0,_o0/* Countries.countries864 */,_nZ/* Countries.countries863 */),
_o2/* countries45 */ = new T2(1,_o1/* Countries.countries862 */,_nY/* Countries.countries46 */),
_o3/* countries866 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Chad"));
}),
_o4/* countries867 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TD"));
}),
_o5/* countries865 */ = new T2(0,_o4/* Countries.countries867 */,_o3/* Countries.countries866 */),
_o6/* countries44 */ = new T2(1,_o5/* Countries.countries865 */,_o2/* Countries.countries45 */),
_o7/* countries869 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Central African Republic"));
}),
_o8/* countries870 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CF"));
}),
_o9/* countries868 */ = new T2(0,_o8/* Countries.countries870 */,_o7/* Countries.countries869 */),
_oa/* countries43 */ = new T2(1,_o9/* Countries.countries868 */,_o6/* Countries.countries44 */),
_ob/* countries872 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cayman Islands"));
}),
_oc/* countries873 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KY"));
}),
_od/* countries871 */ = new T2(0,_oc/* Countries.countries873 */,_ob/* Countries.countries872 */),
_oe/* countries42 */ = new T2(1,_od/* Countries.countries871 */,_oa/* Countries.countries43 */),
_of/* countries875 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cape Verde"));
}),
_og/* countries876 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CV"));
}),
_oh/* countries874 */ = new T2(0,_og/* Countries.countries876 */,_of/* Countries.countries875 */),
_oi/* countries41 */ = new T2(1,_oh/* Countries.countries874 */,_oe/* Countries.countries42 */),
_oj/* countries878 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Canada"));
}),
_ok/* countries879 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CA"));
}),
_ol/* countries877 */ = new T2(0,_ok/* Countries.countries879 */,_oj/* Countries.countries878 */),
_om/* countries40 */ = new T2(1,_ol/* Countries.countries877 */,_oi/* Countries.countries41 */),
_on/* countries881 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cameroon"));
}),
_oo/* countries882 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CM"));
}),
_op/* countries880 */ = new T2(0,_oo/* Countries.countries882 */,_on/* Countries.countries881 */),
_oq/* countries39 */ = new T2(1,_op/* Countries.countries880 */,_om/* Countries.countries40 */),
_or/* countries884 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cambodia"));
}),
_os/* countries885 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("KH"));
}),
_ot/* countries883 */ = new T2(0,_os/* Countries.countries885 */,_or/* Countries.countries884 */),
_ou/* countries38 */ = new T2(1,_ot/* Countries.countries883 */,_oq/* Countries.countries39 */),
_ov/* countries887 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burundi"));
}),
_ow/* countries888 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BI"));
}),
_ox/* countries886 */ = new T2(0,_ow/* Countries.countries888 */,_ov/* Countries.countries887 */),
_oy/* countries37 */ = new T2(1,_ox/* Countries.countries886 */,_ou/* Countries.countries38 */),
_oz/* countries890 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Burkina Faso"));
}),
_oA/* countries891 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BF"));
}),
_oB/* countries889 */ = new T2(0,_oA/* Countries.countries891 */,_oz/* Countries.countries890 */),
_oC/* countries36 */ = new T2(1,_oB/* Countries.countries889 */,_oy/* Countries.countries37 */),
_oD/* countries893 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bulgaria"));
}),
_oE/* countries894 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BG"));
}),
_oF/* countries892 */ = new T2(0,_oE/* Countries.countries894 */,_oD/* Countries.countries893 */),
_oG/* countries35 */ = new T2(1,_oF/* Countries.countries892 */,_oC/* Countries.countries36 */),
_oH/* countries896 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brunei Darussalam"));
}),
_oI/* countries897 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BN"));
}),
_oJ/* countries895 */ = new T2(0,_oI/* Countries.countries897 */,_oH/* Countries.countries896 */),
_oK/* countries34 */ = new T2(1,_oJ/* Countries.countries895 */,_oG/* Countries.countries35 */),
_oL/* countries899 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("British Indian Ocean Territory"));
}),
_oM/* countries900 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IO"));
}),
_oN/* countries898 */ = new T2(0,_oM/* Countries.countries900 */,_oL/* Countries.countries899 */),
_oO/* countries33 */ = new T2(1,_oN/* Countries.countries898 */,_oK/* Countries.countries34 */),
_oP/* countries902 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Brazil"));
}),
_oQ/* countries903 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BR"));
}),
_oR/* countries901 */ = new T2(0,_oQ/* Countries.countries903 */,_oP/* Countries.countries902 */),
_oS/* countries32 */ = new T2(1,_oR/* Countries.countries901 */,_oO/* Countries.countries33 */),
_oT/* countries905 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bouvet Island"));
}),
_oU/* countries906 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BV"));
}),
_oV/* countries904 */ = new T2(0,_oU/* Countries.countries906 */,_oT/* Countries.countries905 */),
_oW/* countries31 */ = new T2(1,_oV/* Countries.countries904 */,_oS/* Countries.countries32 */),
_oX/* countries908 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Botswana"));
}),
_oY/* countries909 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BW"));
}),
_oZ/* countries907 */ = new T2(0,_oY/* Countries.countries909 */,_oX/* Countries.countries908 */),
_p0/* countries30 */ = new T2(1,_oZ/* Countries.countries907 */,_oW/* Countries.countries31 */),
_p1/* countries911 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bosnia and Herzegovina"));
}),
_p2/* countries912 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BA"));
}),
_p3/* countries910 */ = new T2(0,_p2/* Countries.countries912 */,_p1/* Countries.countries911 */),
_p4/* countries29 */ = new T2(1,_p3/* Countries.countries910 */,_p0/* Countries.countries30 */),
_p5/* countries914 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bonaire, Sint Eustatius and Saba"));
}),
_p6/* countries915 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BQ"));
}),
_p7/* countries913 */ = new T2(0,_p6/* Countries.countries915 */,_p5/* Countries.countries914 */),
_p8/* countries28 */ = new T2(1,_p7/* Countries.countries913 */,_p4/* Countries.countries29 */),
_p9/* countries917 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bolivia, Plurinational State of"));
}),
_pa/* countries918 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BO"));
}),
_pb/* countries916 */ = new T2(0,_pa/* Countries.countries918 */,_p9/* Countries.countries917 */),
_pc/* countries27 */ = new T2(1,_pb/* Countries.countries916 */,_p8/* Countries.countries28 */),
_pd/* countries920 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bhutan"));
}),
_pe/* countries921 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BT"));
}),
_pf/* countries919 */ = new T2(0,_pe/* Countries.countries921 */,_pd/* Countries.countries920 */),
_pg/* countries26 */ = new T2(1,_pf/* Countries.countries919 */,_pc/* Countries.countries27 */),
_ph/* countries923 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bermuda"));
}),
_pi/* countries924 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BM"));
}),
_pj/* countries922 */ = new T2(0,_pi/* Countries.countries924 */,_ph/* Countries.countries923 */),
_pk/* countries25 */ = new T2(1,_pj/* Countries.countries922 */,_pg/* Countries.countries26 */),
_pl/* countries926 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Benin"));
}),
_pm/* countries927 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BJ"));
}),
_pn/* countries925 */ = new T2(0,_pm/* Countries.countries927 */,_pl/* Countries.countries926 */),
_po/* countries24 */ = new T2(1,_pn/* Countries.countries925 */,_pk/* Countries.countries25 */),
_pp/* countries929 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belize"));
}),
_pq/* countries930 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BZ"));
}),
_pr/* countries928 */ = new T2(0,_pq/* Countries.countries930 */,_pp/* Countries.countries929 */),
_ps/* countries23 */ = new T2(1,_pr/* Countries.countries928 */,_po/* Countries.countries24 */),
_pt/* countries932 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belgium"));
}),
_pu/* countries933 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BE"));
}),
_pv/* countries931 */ = new T2(0,_pu/* Countries.countries933 */,_pt/* Countries.countries932 */),
_pw/* countries22 */ = new T2(1,_pv/* Countries.countries931 */,_ps/* Countries.countries23 */),
_px/* countries935 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Belarus"));
}),
_py/* countries936 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BY"));
}),
_pz/* countries934 */ = new T2(0,_py/* Countries.countries936 */,_px/* Countries.countries935 */),
_pA/* countries21 */ = new T2(1,_pz/* Countries.countries934 */,_pw/* Countries.countries22 */),
_pB/* countries938 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Barbados"));
}),
_pC/* countries939 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BB"));
}),
_pD/* countries937 */ = new T2(0,_pC/* Countries.countries939 */,_pB/* Countries.countries938 */),
_pE/* countries20 */ = new T2(1,_pD/* Countries.countries937 */,_pA/* Countries.countries21 */),
_pF/* countries941 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bangladesh"));
}),
_pG/* countries942 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BD"));
}),
_pH/* countries940 */ = new T2(0,_pG/* Countries.countries942 */,_pF/* Countries.countries941 */),
_pI/* countries19 */ = new T2(1,_pH/* Countries.countries940 */,_pE/* Countries.countries20 */),
_pJ/* countries944 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahrain"));
}),
_pK/* countries945 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BH"));
}),
_pL/* countries943 */ = new T2(0,_pK/* Countries.countries945 */,_pJ/* Countries.countries944 */),
_pM/* countries18 */ = new T2(1,_pL/* Countries.countries943 */,_pI/* Countries.countries19 */),
_pN/* countries947 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Bahamas"));
}),
_pO/* countries948 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_pP/* countries946 */ = new T2(0,_pO/* Countries.countries948 */,_pN/* Countries.countries947 */),
_pQ/* countries17 */ = new T2(1,_pP/* Countries.countries946 */,_pM/* Countries.countries18 */),
_pR/* countries950 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Azerbaijan"));
}),
_pS/* countries951 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AZ"));
}),
_pT/* countries949 */ = new T2(0,_pS/* Countries.countries951 */,_pR/* Countries.countries950 */),
_pU/* countries16 */ = new T2(1,_pT/* Countries.countries949 */,_pQ/* Countries.countries17 */),
_pV/* countries953 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Austria"));
}),
_pW/* countries954 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AT"));
}),
_pX/* countries952 */ = new T2(0,_pW/* Countries.countries954 */,_pV/* Countries.countries953 */),
_pY/* countries15 */ = new T2(1,_pX/* Countries.countries952 */,_pU/* Countries.countries16 */),
_pZ/* countries956 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Australia"));
}),
_q0/* countries957 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AU"));
}),
_q1/* countries955 */ = new T2(0,_q0/* Countries.countries957 */,_pZ/* Countries.countries956 */),
_q2/* countries14 */ = new T2(1,_q1/* Countries.countries955 */,_pY/* Countries.countries15 */),
_q3/* countries959 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Aruba"));
}),
_q4/* countries960 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AW"));
}),
_q5/* countries958 */ = new T2(0,_q4/* Countries.countries960 */,_q3/* Countries.countries959 */),
_q6/* countries13 */ = new T2(1,_q5/* Countries.countries958 */,_q2/* Countries.countries14 */),
_q7/* countries962 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Armenia"));
}),
_q8/* countries963 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AM"));
}),
_q9/* countries961 */ = new T2(0,_q8/* Countries.countries963 */,_q7/* Countries.countries962 */),
_qa/* countries12 */ = new T2(1,_q9/* Countries.countries961 */,_q6/* Countries.countries13 */),
_qb/* countries965 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Argentina"));
}),
_qc/* countries966 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AR"));
}),
_qd/* countries964 */ = new T2(0,_qc/* Countries.countries966 */,_qb/* Countries.countries965 */),
_qe/* countries11 */ = new T2(1,_qd/* Countries.countries964 */,_qa/* Countries.countries12 */),
_qf/* countries968 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antigua and Barbuda"));
}),
_qg/* countries969 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AG"));
}),
_qh/* countries967 */ = new T2(0,_qg/* Countries.countries969 */,_qf/* Countries.countries968 */),
_qi/* countries10 */ = new T2(1,_qh/* Countries.countries967 */,_qe/* Countries.countries11 */),
_qj/* countries971 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Antarctica"));
}),
_qk/* countries972 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AQ"));
}),
_ql/* countries970 */ = new T2(0,_qk/* Countries.countries972 */,_qj/* Countries.countries971 */),
_qm/* countries9 */ = new T2(1,_ql/* Countries.countries970 */,_qi/* Countries.countries10 */),
_qn/* countries974 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Anguilla"));
}),
_qo/* countries975 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AI"));
}),
_qp/* countries973 */ = new T2(0,_qo/* Countries.countries975 */,_qn/* Countries.countries974 */),
_qq/* countries8 */ = new T2(1,_qp/* Countries.countries973 */,_qm/* Countries.countries9 */),
_qr/* countries977 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Angola"));
}),
_qs/* countries978 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AO"));
}),
_qt/* countries976 */ = new T2(0,_qs/* Countries.countries978 */,_qr/* Countries.countries977 */),
_qu/* countries7 */ = new T2(1,_qt/* Countries.countries976 */,_qq/* Countries.countries8 */),
_qv/* countries980 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Andorra"));
}),
_qw/* countries981 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AD"));
}),
_qx/* countries979 */ = new T2(0,_qw/* Countries.countries981 */,_qv/* Countries.countries980 */),
_qy/* countries6 */ = new T2(1,_qx/* Countries.countries979 */,_qu/* Countries.countries7 */),
_qz/* countries983 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("American Samoa"));
}),
_qA/* countries984 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AS"));
}),
_qB/* countries982 */ = new T2(0,_qA/* Countries.countries984 */,_qz/* Countries.countries983 */),
_qC/* countries5 */ = new T2(1,_qB/* Countries.countries982 */,_qy/* Countries.countries6 */),
_qD/* countries986 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Algeria"));
}),
_qE/* countries987 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DZ"));
}),
_qF/* countries985 */ = new T2(0,_qE/* Countries.countries987 */,_qD/* Countries.countries986 */),
_qG/* countries4 */ = new T2(1,_qF/* Countries.countries985 */,_qC/* Countries.countries5 */),
_qH/* countries989 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Albania"));
}),
_qI/* countries990 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AL"));
}),
_qJ/* countries988 */ = new T2(0,_qI/* Countries.countries990 */,_qH/* Countries.countries989 */),
_qK/* countries3 */ = new T2(1,_qJ/* Countries.countries988 */,_qG/* Countries.countries4 */),
_qL/* countries992 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u00c5land Islands"));
}),
_qM/* countries993 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AX"));
}),
_qN/* countries991 */ = new T2(0,_qM/* Countries.countries993 */,_qL/* Countries.countries992 */),
_qO/* countries2 */ = new T2(1,_qN/* Countries.countries991 */,_qK/* Countries.countries3 */),
_qP/* countries995 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Afghanistan"));
}),
_qQ/* countries996 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("AF"));
}),
_qR/* countries994 */ = new T2(0,_qQ/* Countries.countries996 */,_qP/* Countries.countries995 */),
_qS/* countries1 */ = new T2(1,_qR/* Countries.countries994 */,_qO/* Countries.countries2 */),
_qT/* countries998 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("--select--"));
}),
_qU/* countries997 */ = new T2(0,_I/* GHC.Types.[] */,_qT/* Countries.countries998 */),
_qV/* countries */ = new T2(1,_qU/* Countries.countries997 */,_qS/* Countries.countries1 */),
_qW/* ch0GeneralInformation39 */ = new T2(6,_aO/* FormStructure.Chapter0.ch0GeneralInformation40 */,_qV/* Countries.countries */),
_qX/* ch0GeneralInformation38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institution name"));
}),
_qY/* ch0GeneralInformation37 */ = new T1(1,_qX/* FormStructure.Chapter0.ch0GeneralInformation38 */),
_qZ/* ch0GeneralInformation36 */ = {_:0,a:_qY/* FormStructure.Chapter0.ch0GeneralInformation37 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_r0/* ch0GeneralInformation35 */ = new T1(0,_qZ/* FormStructure.Chapter0.ch0GeneralInformation36 */),
_r1/* ch0GeneralInformation34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Organisation unit"));
}),
_r2/* ch0GeneralInformation33 */ = new T1(1,_r1/* FormStructure.Chapter0.ch0GeneralInformation34 */),
_r3/* ch0GeneralInformation32 */ = {_:0,a:_r2/* FormStructure.Chapter0.ch0GeneralInformation33 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_r4/* ch0GeneralInformation31 */ = new T1(0,_r3/* FormStructure.Chapter0.ch0GeneralInformation32 */),
_r5/* ch0GeneralInformation21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("research group"));
}),
_r6/* ch0GeneralInformation20 */ = new T1(0,_r5/* FormStructure.Chapter0.ch0GeneralInformation21 */),
_r7/* ch0GeneralInformation19 */ = new T2(1,_r6/* FormStructure.Chapter0.ch0GeneralInformation20 */,_I/* GHC.Types.[] */),
_r8/* ch0GeneralInformation23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("department"));
}),
_r9/* ch0GeneralInformation22 */ = new T1(0,_r8/* FormStructure.Chapter0.ch0GeneralInformation23 */),
_ra/* ch0GeneralInformation18 */ = new T2(1,_r9/* FormStructure.Chapter0.ch0GeneralInformation22 */,_r7/* FormStructure.Chapter0.ch0GeneralInformation19 */),
_rb/* ch0GeneralInformation25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("faculty"));
}),
_rc/* ch0GeneralInformation24 */ = new T1(0,_rb/* FormStructure.Chapter0.ch0GeneralInformation25 */),
_rd/* ch0GeneralInformation17 */ = new T2(1,_rc/* FormStructure.Chapter0.ch0GeneralInformation24 */,_ra/* FormStructure.Chapter0.ch0GeneralInformation18 */),
_re/* ch0GeneralInformation27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution"));
}),
_rf/* ch0GeneralInformation26 */ = new T1(0,_re/* FormStructure.Chapter0.ch0GeneralInformation27 */),
_rg/* ch0GeneralInformation16 */ = new T2(1,_rf/* FormStructure.Chapter0.ch0GeneralInformation26 */,_rd/* FormStructure.Chapter0.ch0GeneralInformation17 */),
_rh/* ch0GeneralInformation30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Level of unit"));
}),
_ri/* ch0GeneralInformation29 */ = new T1(1,_rh/* FormStructure.Chapter0.ch0GeneralInformation30 */),
_rj/* ch0GeneralInformation28 */ = {_:0,a:_ri/* FormStructure.Chapter0.ch0GeneralInformation29 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rk/* ch0GeneralInformation15 */ = new T2(5,_rj/* FormStructure.Chapter0.ch0GeneralInformation28 */,_rg/* FormStructure.Chapter0.ch0GeneralInformation16 */),
_rl/* ch0GeneralInformation11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("This is informational form item. It just displays the given text. Let us write something more, so we see, how this renders."));
}),
_rm/* ch0GeneralInformation14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sample informational form item."));
}),
_rn/* ch0GeneralInformation13 */ = new T1(1,_rm/* FormStructure.Chapter0.ch0GeneralInformation14 */),
_ro/* ch0GeneralInformation12 */ = {_:0,a:_rn/* FormStructure.Chapter0.ch0GeneralInformation13 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rp/* ch0GeneralInformation10 */ = new T2(4,_ro/* FormStructure.Chapter0.ch0GeneralInformation12 */,_rl/* FormStructure.Chapter0.ch0GeneralInformation11 */),
_rq/* ch0GeneralInformation9 */ = new T2(1,_rp/* FormStructure.Chapter0.ch0GeneralInformation10 */,_I/* GHC.Types.[] */),
_rr/* ch0GeneralInformation8 */ = new T2(1,_rk/* FormStructure.Chapter0.ch0GeneralInformation15 */,_rq/* FormStructure.Chapter0.ch0GeneralInformation9 */),
_rs/* ch0GeneralInformation7 */ = new T2(1,_r4/* FormStructure.Chapter0.ch0GeneralInformation31 */,_rr/* FormStructure.Chapter0.ch0GeneralInformation8 */),
_rt/* ch0GeneralInformation6 */ = new T2(1,_r0/* FormStructure.Chapter0.ch0GeneralInformation35 */,_rs/* FormStructure.Chapter0.ch0GeneralInformation7 */),
_ru/* ch0GeneralInformation5 */ = new T2(1,_qW/* FormStructure.Chapter0.ch0GeneralInformation39 */,_rt/* FormStructure.Chapter0.ch0GeneralInformation6 */),
_rv/* ch0GeneralInformation4 */ = new T3(8,_aL/* FormStructure.Chapter0.ch0GeneralInformation44 */,_aI/* FormStructure.Chapter0.ch0GeneralInformation43 */,_ru/* FormStructure.Chapter0.ch0GeneralInformation5 */),
_rw/* ch0GeneralInformation2 */ = new T2(1,_rv/* FormStructure.Chapter0.ch0GeneralInformation4 */,_aH/* FormStructure.Chapter0.ch0GeneralInformation3 */),
_rx/* ch0GeneralInformation54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Email"));
}),
_ry/* ch0GeneralInformation53 */ = new T1(1,_rx/* FormStructure.Chapter0.ch0GeneralInformation54 */),
_rz/* ch0GeneralInformation52 */ = {_:0,a:_ry/* FormStructure.Chapter0.ch0GeneralInformation53 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rA/* ch0GeneralInformation51 */ = new T1(2,_rz/* FormStructure.Chapter0.ch0GeneralInformation52 */),
_rB/* ch0GeneralInformation50 */ = new T2(1,_rA/* FormStructure.Chapter0.ch0GeneralInformation51 */,_I/* GHC.Types.[] */),
_rC/* ch0GeneralInformation58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Surname"));
}),
_rD/* ch0GeneralInformation57 */ = new T1(1,_rC/* FormStructure.Chapter0.ch0GeneralInformation58 */),
_rE/* ch0GeneralInformation56 */ = {_:0,a:_rD/* FormStructure.Chapter0.ch0GeneralInformation57 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rF/* ch0GeneralInformation55 */ = new T1(0,_rE/* FormStructure.Chapter0.ch0GeneralInformation56 */),
_rG/* ch0GeneralInformation49 */ = new T2(1,_rF/* FormStructure.Chapter0.ch0GeneralInformation55 */,_rB/* FormStructure.Chapter0.ch0GeneralInformation50 */),
_rH/* ch0GeneralInformation62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("First name"));
}),
_rI/* ch0GeneralInformation61 */ = new T1(1,_rH/* FormStructure.Chapter0.ch0GeneralInformation62 */),
_rJ/* ch0GeneralInformation60 */ = {_:0,a:_rI/* FormStructure.Chapter0.ch0GeneralInformation61 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rK/* ch0GeneralInformation59 */ = new T1(0,_rJ/* FormStructure.Chapter0.ch0GeneralInformation60 */),
_rL/* ch0GeneralInformation48 */ = new T2(1,_rK/* FormStructure.Chapter0.ch0GeneralInformation59 */,_rG/* FormStructure.Chapter0.ch0GeneralInformation49 */),
_rM/* ch0GeneralInformation65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Registration of the responder"));
}),
_rN/* ch0GeneralInformation64 */ = new T1(1,_rM/* FormStructure.Chapter0.ch0GeneralInformation65 */),
_rO/* ch0GeneralInformation63 */ = {_:0,a:_rN/* FormStructure.Chapter0.ch0GeneralInformation64 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rP/* ch0GeneralInformation47 */ = new T3(8,_rO/* FormStructure.Chapter0.ch0GeneralInformation63 */,_aI/* FormStructure.Chapter0.ch0GeneralInformation43 */,_rL/* FormStructure.Chapter0.ch0GeneralInformation48 */),
_rQ/* ch0GeneralInformation1 */ = new T2(1,_rP/* FormStructure.Chapter0.ch0GeneralInformation47 */,_rw/* FormStructure.Chapter0.ch0GeneralInformation2 */),
_rR/* ch0GeneralInformation68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("0.General Info"));
}),
_rS/* ch0GeneralInformation67 */ = new T1(1,_rR/* FormStructure.Chapter0.ch0GeneralInformation68 */),
_rT/* ch0GeneralInformation66 */ = {_:0,a:_rS/* FormStructure.Chapter0.ch0GeneralInformation67 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_rU/* ch0GeneralInformation */ = new T2(7,_rT/* FormStructure.Chapter0.ch0GeneralInformation66 */,_rQ/* FormStructure.Chapter0.ch0GeneralInformation1 */),
_rV/* ch1DataProduction226 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you produce raw data?"));
}),
_rW/* ch1DataProduction225 */ = new T1(1,_rV/* FormStructure.Chapter1.ch1DataProduction226 */),
_rX/* ch1DataProduction224 */ = {_:0,a:_rW/* FormStructure.Chapter1.ch1DataProduction225 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_rY/* ch1DataProduction6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_rZ/* ch1DataProduction5 */ = new T1(0,_rY/* FormStructure.Chapter1.ch1DataProduction6 */),
_s0/* ch1DataProduction4 */ = new T2(1,_rZ/* FormStructure.Chapter1.ch1DataProduction5 */,_I/* GHC.Types.[] */),
_s1/* ch1DataProduction223 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_s2/* ch1DataProduction123 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_s3/* ch1DataProduction122 */ = new T1(0,_s2/* FormStructure.Chapter1.ch1DataProduction123 */),
_s4/* ReadOnlyRule */ = new T0(3),
_s5/* ch1DataProduction125 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_s6/* ch1DataProduction127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-sum"));
}),
_s7/* ch1DataProduction126 */ = new T1(1,_s6/* FormStructure.Chapter1.ch1DataProduction127 */),
_s8/* ch1DataProduction129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production cost"));
}),
_s9/* ch1DataProduction128 */ = new T1(1,_s8/* FormStructure.Chapter1.ch1DataProduction129 */),
_sa/* ch1DataProduction124 */ = {_:0,a:_s9/* FormStructure.Chapter1.ch1DataProduction128 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_s7/* FormStructure.Chapter1.ch1DataProduction126 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_s5/* FormStructure.Chapter1.ch1DataProduction125 */},
_sb/* ch1DataProduction121 */ = new T2(3,_sa/* FormStructure.Chapter1.ch1DataProduction124 */,_s3/* FormStructure.Chapter1.ch1DataProduction122 */),
_sc/* ch1DataProduction120 */ = new T2(1,_sb/* FormStructure.Chapter1.ch1DataProduction121 */,_I/* GHC.Types.[] */),
_sd/* ch1DataProduction132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_se/* ch1DataProduction131 */ = new T1(0,_sd/* FormStructure.Chapter1.ch1DataProduction132 */),
_sf/* totalSum1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_sg/* totalSum11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_sh/* totalSum10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_si/* totalSum7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_sj/* totalSum6 */ = new T2(1,_si/* FormStructure.Common.totalSum7 */,_I/* GHC.Types.[] */),
_sk/* totalSum8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_sl/* totalSum5 */ = new T2(1,_sk/* FormStructure.Common.totalSum8 */,_sj/* FormStructure.Common.totalSum6 */),
_sm/* totalSum9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_sn/* totalSum4 */ = new T2(1,_sm/* FormStructure.Common.totalSum9 */,_sl/* FormStructure.Common.totalSum5 */),
_so/* totalSum3 */ = new T2(1,_sh/* FormStructure.Common.totalSum10 */,_sn/* FormStructure.Common.totalSum4 */),
_sp/* totalSum2 */ = new T2(1,_sg/* FormStructure.Common.totalSum11 */,_so/* FormStructure.Common.totalSum3 */),
_sq/* totalSum */ = new T2(1,_sp/* FormStructure.Common.totalSum2 */,_sf/* FormStructure.Common.totalSum1 */),
_sr/* ch1DataProduction135 */ = new T2(1,_sq/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_ss/* ch1DataProduction134 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_sr/* FormStructure.Chapter1.ch1DataProduction135 */),
_st/* ch1DataProduction137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-sum"));
}),
_su/* ch1DataProduction136 */ = new T1(1,_st/* FormStructure.Chapter1.ch1DataProduction137 */),
_sv/* ch1DataProduction139 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Raw data production volume"));
}),
_sw/* ch1DataProduction138 */ = new T1(1,_sv/* FormStructure.Chapter1.ch1DataProduction139 */),
_sx/* ch1DataProduction133 */ = {_:0,a:_sw/* FormStructure.Chapter1.ch1DataProduction138 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_su/* FormStructure.Chapter1.ch1DataProduction136 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_ss/* FormStructure.Chapter1.ch1DataProduction134 */},
_sy/* ch1DataProduction130 */ = new T2(3,_sx/* FormStructure.Chapter1.ch1DataProduction133 */,_se/* FormStructure.Chapter1.ch1DataProduction131 */),
_sz/* ch1DataProduction119 */ = new T2(1,_sy/* FormStructure.Chapter1.ch1DataProduction130 */,_sc/* FormStructure.Chapter1.ch1DataProduction120 */),
_sA/* ch1DataProduction150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-others"));
}),
_sB/* ch1DataProduction149 */ = new T2(1,_sA/* FormStructure.Chapter1.ch1DataProduction150 */,_I/* GHC.Types.[] */),
_sC/* ch1DataProduction151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-proteomics"));
}),
_sD/* ch1DataProduction148 */ = new T2(1,_sC/* FormStructure.Chapter1.ch1DataProduction151 */,_sB/* FormStructure.Chapter1.ch1DataProduction149 */),
_sE/* ch1DataProduction152 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-cost-genomics"));
}),
_sF/* ch1DataProduction147 */ = new T2(1,_sE/* FormStructure.Chapter1.ch1DataProduction152 */,_sD/* FormStructure.Chapter1.ch1DataProduction148 */),
_sG/* ch1DataProduction_costSumRule */ = new T2(0,_sF/* FormStructure.Chapter1.ch1DataProduction147 */,_s6/* FormStructure.Chapter1.ch1DataProduction127 */),
_sH/* ch1DataProduction146 */ = new T2(1,_sG/* FormStructure.Chapter1.ch1DataProduction_costSumRule */,_I/* GHC.Types.[] */),
_sI/* ch1DataProduction154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_sJ/* ch1DataProduction153 */ = new T1(1,_sI/* FormStructure.Chapter1.ch1DataProduction154 */),
_sK/* ch1DataProduction155 */ = new T1(1,_sA/* FormStructure.Chapter1.ch1DataProduction150 */),
_sL/* ch1DataProduction157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost for year 2015"));
}),
_sM/* ch1DataProduction156 */ = new T1(1,_sL/* FormStructure.Chapter1.ch1DataProduction157 */),
_sN/* ch1DataProduction145 */ = {_:0,a:_sM/* FormStructure.Chapter1.ch1DataProduction156 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_sK/* FormStructure.Chapter1.ch1DataProduction155 */,d:_I/* GHC.Types.[] */,e:_sJ/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_sH/* FormStructure.Chapter1.ch1DataProduction146 */},
_sO/* ch1DataProduction144 */ = new T2(3,_sN/* FormStructure.Chapter1.ch1DataProduction145 */,_s3/* FormStructure.Chapter1.ch1DataProduction122 */),
_sP/* ch1DataProduction143 */ = new T2(1,_sO/* FormStructure.Chapter1.ch1DataProduction144 */,_I/* GHC.Types.[] */),
_sQ/* ch1DataProduction164 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_sR/* ch1DataProduction163 */ = new T2(1,_sQ/* FormStructure.Chapter1.ch1DataProduction164 */,_I/* GHC.Types.[] */),
_sS/* ch1DataProduction162 */ = new T2(1,_sd/* FormStructure.Chapter1.ch1DataProduction132 */,_sR/* FormStructure.Chapter1.ch1DataProduction163 */),
_sT/* ch1DataProduction165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_sU/* ch1DataProduction161 */ = new T2(1,_sT/* FormStructure.Chapter1.ch1DataProduction165 */,_sS/* FormStructure.Chapter1.ch1DataProduction162 */),
_sV/* ch1DataProduction166 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_sW/* ch1DataProduction160 */ = new T2(1,_sV/* FormStructure.Chapter1.ch1DataProduction166 */,_sU/* FormStructure.Chapter1.ch1DataProduction161 */),
_sX/* ch1DataProduction159 */ = new T1(1,_sW/* FormStructure.Chapter1.ch1DataProduction160 */),
_sY/* ch1DataProduction180 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_sZ/* ch1DataProduction179 */ = new T2(1,_sY/* FormStructure.Chapter1.ch1DataProduction180 */,_I/* GHC.Types.[] */),
_t0/* ch1DataProduction181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_t1/* ch1DataProduction178 */ = new T2(1,_t0/* FormStructure.Chapter1.ch1DataProduction181 */,_sZ/* FormStructure.Chapter1.ch1DataProduction179 */),
_t2/* ch1DataProduction175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-others"));
}),
_t3/* ch1DataProduction182 */ = new T1(1,_t2/* FormStructure.Chapter1.ch1DataProduction175 */),
_t4/* ch1DataProduction184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Volume"));
}),
_t5/* ch1DataProduction183 */ = new T1(1,_t4/* FormStructure.Chapter1.ch1DataProduction184 */),
_t6/* ch1DataProduction170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_t7/* ch1DataProduction169 */ = new T2(2,_st/* FormStructure.Chapter1.ch1DataProduction137 */,_t6/* FormStructure.Chapter1.ch1DataProduction170 */),
_t8/* ch1DataProduction168 */ = new T2(1,_t7/* FormStructure.Chapter1.ch1DataProduction169 */,_I/* GHC.Types.[] */),
_t9/* ch1DataProduction174 */ = new T2(1,_t2/* FormStructure.Chapter1.ch1DataProduction175 */,_I/* GHC.Types.[] */),
_ta/* ch1DataProduction176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-proteomics"));
}),
_tb/* ch1DataProduction173 */ = new T2(1,_ta/* FormStructure.Chapter1.ch1DataProduction176 */,_t9/* FormStructure.Chapter1.ch1DataProduction174 */),
_tc/* ch1DataProduction177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-volume-genomics"));
}),
_td/* ch1DataProduction172 */ = new T2(1,_tc/* FormStructure.Chapter1.ch1DataProduction177 */,_tb/* FormStructure.Chapter1.ch1DataProduction173 */),
_te/* ch1DataProduction171 */ = new T2(1,_td/* FormStructure.Chapter1.ch1DataProduction172 */,_st/* FormStructure.Chapter1.ch1DataProduction137 */),
_tf/* ch1DataProduction_volumeSumRules */ = new T2(1,_te/* FormStructure.Chapter1.ch1DataProduction171 */,_t8/* FormStructure.Chapter1.ch1DataProduction168 */),
_tg/* ch1DataProduction167 */ = {_:0,a:_t5/* FormStructure.Chapter1.ch1DataProduction183 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_t3/* FormStructure.Chapter1.ch1DataProduction182 */,d:_t1/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_tf/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_th/* ch1DataProduction158 */ = new T2(3,_tg/* FormStructure.Chapter1.ch1DataProduction167 */,_sX/* FormStructure.Chapter1.ch1DataProduction159 */),
_ti/* ch1DataProduction142 */ = new T2(1,_th/* FormStructure.Chapter1.ch1DataProduction158 */,_sP/* FormStructure.Chapter1.ch1DataProduction143 */),
_tj/* ch1DataProduction188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Images, chips, spectra, ..."));
}),
_tk/* ch1DataProduction187 */ = new T1(1,_tj/* FormStructure.Chapter1.ch1DataProduction188 */),
_tl/* ch1DataProduction190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Specify the output type of raw data"));
}),
_tm/* ch1DataProduction189 */ = new T1(1,_tl/* FormStructure.Chapter1.ch1DataProduction190 */),
_tn/* ch1DataProduction186 */ = {_:0,a:_tm/* FormStructure.Chapter1.ch1DataProduction189 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_tk/* FormStructure.Chapter1.ch1DataProduction187 */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_to/* ch1DataProduction185 */ = new T1(0,_tn/* FormStructure.Chapter1.ch1DataProduction186 */),
_tp/* ch1DataProduction141 */ = new T2(1,_to/* FormStructure.Chapter1.ch1DataProduction185 */,_ti/* FormStructure.Chapter1.ch1DataProduction142 */),
_tq/* ch1DataProduction193 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Others"));
}),
_tr/* ch1DataProduction192 */ = new T1(1,_tq/* FormStructure.Chapter1.ch1DataProduction193 */),
_ts/* ch1DataProduction191 */ = {_:0,a:_tr/* FormStructure.Chapter1.ch1DataProduction192 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tt/* ch1DataProduction67 */ = 0,
_tu/* ch1DataProduction140 */ = new T3(9,_ts/* FormStructure.Chapter1.ch1DataProduction191 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_tp/* FormStructure.Chapter1.ch1DataProduction141 */),
_tv/* ch1DataProduction118 */ = new T2(1,_tu/* FormStructure.Chapter1.ch1DataProduction140 */,_sz/* FormStructure.Chapter1.ch1DataProduction119 */),
_tw/* ch1DataProduction199 */ = new T1(1,_sC/* FormStructure.Chapter1.ch1DataProduction151 */),
_tx/* ch1DataProduction198 */ = {_:0,a:_sM/* FormStructure.Chapter1.ch1DataProduction156 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_tw/* FormStructure.Chapter1.ch1DataProduction199 */,d:_I/* GHC.Types.[] */,e:_sJ/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_sH/* FormStructure.Chapter1.ch1DataProduction146 */},
_ty/* ch1DataProduction197 */ = new T2(3,_tx/* FormStructure.Chapter1.ch1DataProduction198 */,_s3/* FormStructure.Chapter1.ch1DataProduction122 */),
_tz/* ch1DataProduction196 */ = new T2(1,_ty/* FormStructure.Chapter1.ch1DataProduction197 */,_I/* GHC.Types.[] */),
_tA/* ch1DataProduction202 */ = new T1(1,_ta/* FormStructure.Chapter1.ch1DataProduction176 */),
_tB/* ch1DataProduction201 */ = {_:0,a:_t5/* FormStructure.Chapter1.ch1DataProduction183 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_tA/* FormStructure.Chapter1.ch1DataProduction202 */,d:_t1/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_tf/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_tC/* ch1DataProduction200 */ = new T2(3,_tB/* FormStructure.Chapter1.ch1DataProduction201 */,_sX/* FormStructure.Chapter1.ch1DataProduction159 */),
_tD/* ch1DataProduction195 */ = new T2(1,_tC/* FormStructure.Chapter1.ch1DataProduction200 */,_tz/* FormStructure.Chapter1.ch1DataProduction196 */),
_tE/* ch1DataProduction205 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Proteomics"));
}),
_tF/* ch1DataProduction204 */ = new T1(1,_tE/* FormStructure.Chapter1.ch1DataProduction205 */),
_tG/* ch1DataProduction203 */ = {_:0,a:_tF/* FormStructure.Chapter1.ch1DataProduction204 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tH/* ch1DataProduction194 */ = new T3(9,_tG/* FormStructure.Chapter1.ch1DataProduction203 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_tD/* FormStructure.Chapter1.ch1DataProduction195 */),
_tI/* ch1DataProduction117 */ = new T2(1,_tH/* FormStructure.Chapter1.ch1DataProduction194 */,_tv/* FormStructure.Chapter1.ch1DataProduction118 */),
_tJ/* ch1DataProduction211 */ = new T1(1,_sE/* FormStructure.Chapter1.ch1DataProduction152 */),
_tK/* ch1DataProduction210 */ = {_:0,a:_sM/* FormStructure.Chapter1.ch1DataProduction156 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_tJ/* FormStructure.Chapter1.ch1DataProduction211 */,d:_I/* GHC.Types.[] */,e:_sJ/* FormStructure.Chapter1.ch1DataProduction153 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_sH/* FormStructure.Chapter1.ch1DataProduction146 */},
_tL/* ch1DataProduction209 */ = new T2(3,_tK/* FormStructure.Chapter1.ch1DataProduction210 */,_s3/* FormStructure.Chapter1.ch1DataProduction122 */),
_tM/* ch1DataProduction208 */ = new T2(1,_tL/* FormStructure.Chapter1.ch1DataProduction209 */,_I/* GHC.Types.[] */),
_tN/* ch1DataProduction214 */ = new T1(1,_tc/* FormStructure.Chapter1.ch1DataProduction177 */),
_tO/* ch1DataProduction213 */ = {_:0,a:_t5/* FormStructure.Chapter1.ch1DataProduction183 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_tN/* FormStructure.Chapter1.ch1DataProduction214 */,d:_t1/* FormStructure.Chapter1.ch1DataProduction178 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_tf/* FormStructure.Chapter1.ch1DataProduction_volumeSumRules */},
_tP/* ch1DataProduction212 */ = new T2(3,_tO/* FormStructure.Chapter1.ch1DataProduction213 */,_sX/* FormStructure.Chapter1.ch1DataProduction159 */),
_tQ/* ch1DataProduction207 */ = new T2(1,_tP/* FormStructure.Chapter1.ch1DataProduction212 */,_tM/* FormStructure.Chapter1.ch1DataProduction208 */),
_tR/* ch1DataProduction217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Genomics"));
}),
_tS/* ch1DataProduction216 */ = new T1(1,_tR/* FormStructure.Chapter1.ch1DataProduction217 */),
_tT/* ch1DataProduction215 */ = {_:0,a:_tS/* FormStructure.Chapter1.ch1DataProduction216 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_tU/* ch1DataProduction206 */ = new T3(9,_tT/* FormStructure.Chapter1.ch1DataProduction215 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_tQ/* FormStructure.Chapter1.ch1DataProduction207 */),
_tV/* ch1DataProduction116 */ = new T2(1,_tU/* FormStructure.Chapter1.ch1DataProduction206 */,_tI/* FormStructure.Chapter1.ch1DataProduction117 */),
_tW/* ch1DataProduction220 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("(Estimated) volume of raw data produced inhouse in 2015"));
}),
_tX/* ch1DataProduction219 */ = new T1(1,_tW/* FormStructure.Chapter1.ch1DataProduction220 */),
_tY/* ch1DataProduction222 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Type of data"));
}),
_tZ/* ch1DataProduction221 */ = new T1(1,_tY/* FormStructure.Chapter1.ch1DataProduction222 */),
_u0/* ch1DataProduction218 */ = {_:0,a:_tZ/* FormStructure.Chapter1.ch1DataProduction221 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_tX/* FormStructure.Chapter1.ch1DataProduction219 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_u1/* ch1DataProduction115 */ = new T3(8,_u0/* FormStructure.Chapter1.ch1DataProduction218 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_tV/* FormStructure.Chapter1.ch1DataProduction116 */),
_u2/* ch1DataProduction11 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_u3/* ch1DataProduction19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_u4/* ch1DataProduction18 */ = new T1(0,_u3/* FormStructure.Chapter1.ch1DataProduction19 */),
_u5/* ch1DataProduction24 */ = function(_u6/* sand */){
  return (E(_u6/* sand */)==100) ? true : false;
},
_u7/* ch1DataProduction23 */ = new T1(4,_u5/* FormStructure.Chapter1.ch1DataProduction24 */),
_u8/* ch1DataProduction22 */ = new T2(1,_u7/* FormStructure.Chapter1.ch1DataProduction23 */,_I/* GHC.Types.[] */),
_u9/* ch1DataProduction21 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_u8/* FormStructure.Chapter1.ch1DataProduction22 */),
_ua/* ch1DataProduction26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-sum"));
}),
_ub/* ch1DataProduction25 */ = new T1(1,_ua/* FormStructure.Chapter1.ch1DataProduction26 */),
_uc/* ch1DataProduction28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_ud/* ch1DataProduction27 */ = new T1(1,_uc/* FormStructure.Chapter1.ch1DataProduction28 */),
_ue/* ch1DataProduction20 */ = {_:0,a:_ud/* FormStructure.Chapter1.ch1DataProduction27 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_ub/* FormStructure.Chapter1.ch1DataProduction25 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_u9/* FormStructure.Chapter1.ch1DataProduction21 */},
_uf/* ch1DataProduction17 */ = new T2(3,_ue/* FormStructure.Chapter1.ch1DataProduction20 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_ug/* ch1DataProduction16 */ = new T2(1,_uf/* FormStructure.Chapter1.ch1DataProduction17 */,_I/* GHC.Types.[] */),
_uh/* ch1DataProduction34 */ = function(_ui/* san7 */){
  var _uj/* san8 */ = E(_ui/* san7 */);
  return (_uj/* san8 */<0) ? false : _uj/* san8 */<=100;
},
_uk/* ch1DataProduction33 */ = new T1(4,_uh/* FormStructure.Chapter1.ch1DataProduction34 */),
_ul/* ch1DataProduction32 */ = new T2(1,_uk/* FormStructure.Chapter1.ch1DataProduction33 */,_I/* GHC.Types.[] */),
_um/* ch1DataProduction38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-open"));
}),
_un/* ch1DataProduction37 */ = new T2(1,_um/* FormStructure.Chapter1.ch1DataProduction38 */,_I/* GHC.Types.[] */),
_uo/* ch1DataProduction39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-closed"));
}),
_up/* ch1DataProduction36 */ = new T2(1,_uo/* FormStructure.Chapter1.ch1DataProduction39 */,_un/* FormStructure.Chapter1.ch1DataProduction37 */),
_uq/* ch1DataProduction40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-accessibility-inside"));
}),
_ur/* ch1DataProduction35 */ = new T2(1,_uq/* FormStructure.Chapter1.ch1DataProduction40 */,_up/* FormStructure.Chapter1.ch1DataProduction36 */),
_us/* ch1DataProduction_accSumRule */ = new T2(0,_ur/* FormStructure.Chapter1.ch1DataProduction35 */,_ua/* FormStructure.Chapter1.ch1DataProduction26 */),
_ut/* ch1DataProduction31 */ = new T2(1,_us/* FormStructure.Chapter1.ch1DataProduction_accSumRule */,_ul/* FormStructure.Chapter1.ch1DataProduction32 */),
_uu/* ch1DataProduction42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_uv/* ch1DataProduction41 */ = new T1(1,_uu/* FormStructure.Chapter1.ch1DataProduction42 */),
_uw/* ch1DataProduction45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_ux/* ch1DataProduction44 */ = new T2(1,_uw/* FormStructure.Chapter1.ch1DataProduction45 */,_I/* GHC.Types.[] */),
_uy/* ch1DataProduction46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_uz/* ch1DataProduction43 */ = new T2(1,_uy/* FormStructure.Chapter1.ch1DataProduction46 */,_ux/* FormStructure.Chapter1.ch1DataProduction44 */),
_uA/* ch1DataProduction47 */ = new T1(1,_um/* FormStructure.Chapter1.ch1DataProduction38 */),
_uB/* ch1DataProduction49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_uC/* ch1DataProduction48 */ = new T1(1,_uB/* FormStructure.Chapter1.ch1DataProduction49 */),
_uD/* ch1DataProduction30 */ = {_:0,a:_uC/* FormStructure.Chapter1.ch1DataProduction48 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_uA/* FormStructure.Chapter1.ch1DataProduction47 */,d:_uz/* FormStructure.Chapter1.ch1DataProduction43 */,e:_uv/* FormStructure.Chapter1.ch1DataProduction41 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_ut/* FormStructure.Chapter1.ch1DataProduction31 */},
_uE/* ch1DataProduction29 */ = new T2(3,_uD/* FormStructure.Chapter1.ch1DataProduction30 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_uF/* ch1DataProduction15 */ = new T2(1,_uE/* FormStructure.Chapter1.ch1DataProduction29 */,_ug/* FormStructure.Chapter1.ch1DataProduction16 */),
_uG/* ch1DataProduction53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_uH/* ch1DataProduction52 */ = new T1(1,_uG/* FormStructure.Chapter1.ch1DataProduction53 */),
_uI/* ch1DataProduction56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_uJ/* ch1DataProduction55 */ = new T2(1,_uI/* FormStructure.Chapter1.ch1DataProduction56 */,_I/* GHC.Types.[] */),
_uK/* ch1DataProduction54 */ = new T2(1,_uy/* FormStructure.Chapter1.ch1DataProduction46 */,_uJ/* FormStructure.Chapter1.ch1DataProduction55 */),
_uL/* ch1DataProduction57 */ = new T1(1,_uo/* FormStructure.Chapter1.ch1DataProduction39 */),
_uM/* ch1DataProduction59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_uN/* ch1DataProduction58 */ = new T1(1,_uM/* FormStructure.Chapter1.ch1DataProduction59 */),
_uO/* ch1DataProduction51 */ = {_:0,a:_uN/* FormStructure.Chapter1.ch1DataProduction58 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_uL/* FormStructure.Chapter1.ch1DataProduction57 */,d:_uK/* FormStructure.Chapter1.ch1DataProduction54 */,e:_uH/* FormStructure.Chapter1.ch1DataProduction52 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_ut/* FormStructure.Chapter1.ch1DataProduction31 */},
_uP/* ch1DataProduction50 */ = new T2(3,_uO/* FormStructure.Chapter1.ch1DataProduction51 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_uQ/* ch1DataProduction14 */ = new T2(1,_uP/* FormStructure.Chapter1.ch1DataProduction50 */,_uF/* FormStructure.Chapter1.ch1DataProduction15 */),
_uR/* ch1DataProduction63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_uS/* ch1DataProduction62 */ = new T2(1,_uR/* FormStructure.Chapter1.ch1DataProduction63 */,_I/* GHC.Types.[] */),
_uT/* ch1DataProduction64 */ = new T1(1,_uq/* FormStructure.Chapter1.ch1DataProduction40 */),
_uU/* ch1DataProduction66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_uV/* ch1DataProduction65 */ = new T1(1,_uU/* FormStructure.Chapter1.ch1DataProduction66 */),
_uW/* ch1DataProduction61 */ = {_:0,a:_uV/* FormStructure.Chapter1.ch1DataProduction65 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_uT/* FormStructure.Chapter1.ch1DataProduction64 */,d:_uS/* FormStructure.Chapter1.ch1DataProduction62 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_ut/* FormStructure.Chapter1.ch1DataProduction31 */},
_uX/* ch1DataProduction60 */ = new T2(3,_uW/* FormStructure.Chapter1.ch1DataProduction61 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_uY/* ch1DataProduction13 */ = new T2(1,_uX/* FormStructure.Chapter1.ch1DataProduction60 */,_uQ/* FormStructure.Chapter1.ch1DataProduction14 */),
_uZ/* ch1DataProduction70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_v0/* ch1DataProduction69 */ = new T1(1,_uZ/* FormStructure.Chapter1.ch1DataProduction70 */),
_v1/* ch1DataProduction68 */ = {_:0,a:_v0/* FormStructure.Chapter1.ch1DataProduction69 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_v2/* ch1DataProduction12 */ = new T3(8,_v1/* FormStructure.Chapter1.ch1DataProduction68 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_uY/* FormStructure.Chapter1.ch1DataProduction13 */),
_v3/* ch1DataProduction10 */ = new T2(1,_v2/* FormStructure.Chapter1.ch1DataProduction12 */,_u2/* FormStructure.Chapter1.ch1DataProduction11 */),
_v4/* ch1DataProduction112 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Skip if you do not want to share"));
}),
_v5/* ch1DataProduction111 */ = new T1(1,_v4/* FormStructure.Chapter1.ch1DataProduction112 */),
_v6/* ch1DataProduction114 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_v7/* ch1DataProduction113 */ = new T1(1,_v6/* FormStructure.Chapter1.ch1DataProduction114 */),
_v8/* ch1DataProduction110 */ = {_:0,a:_v7/* FormStructure.Chapter1.ch1DataProduction113 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_v5/* FormStructure.Chapter1.ch1DataProduction111 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_v9/* ch1DataProduction91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-institutional"));
}),
_va/* ch1DataProduction107 */ = new T1(1,_v9/* FormStructure.Chapter1.ch1DataProduction91 */),
_vb/* ch1DataProduction109 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_vc/* ch1DataProduction108 */ = new T1(1,_vb/* FormStructure.Chapter1.ch1DataProduction109 */),
_vd/* ch1DataProduction80 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-sum"));
}),
_ve/* ch1DataProduction88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-worldwide"));
}),
_vf/* ch1DataProduction87 */ = new T2(1,_ve/* FormStructure.Chapter1.ch1DataProduction88 */,_I/* GHC.Types.[] */),
_vg/* ch1DataProduction89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-european"));
}),
_vh/* ch1DataProduction86 */ = new T2(1,_vg/* FormStructure.Chapter1.ch1DataProduction89 */,_vf/* FormStructure.Chapter1.ch1DataProduction87 */),
_vi/* ch1DataProduction90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("raw-funding-national"));
}),
_vj/* ch1DataProduction85 */ = new T2(1,_vi/* FormStructure.Chapter1.ch1DataProduction90 */,_vh/* FormStructure.Chapter1.ch1DataProduction86 */),
_vk/* ch1DataProduction84 */ = new T2(1,_v9/* FormStructure.Chapter1.ch1DataProduction91 */,_vj/* FormStructure.Chapter1.ch1DataProduction85 */),
_vl/* ch1DataProduction_fundingSumRule */ = new T2(0,_vk/* FormStructure.Chapter1.ch1DataProduction84 */,_vd/* FormStructure.Chapter1.ch1DataProduction80 */),
_vm/* ch1DataProduction83 */ = new T2(1,_vl/* FormStructure.Chapter1.ch1DataProduction_fundingSumRule */,_ul/* FormStructure.Chapter1.ch1DataProduction32 */),
_vn/* ch1DataProduction106 */ = {_:0,a:_vc/* FormStructure.Chapter1.ch1DataProduction108 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_va/* FormStructure.Chapter1.ch1DataProduction107 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_vm/* FormStructure.Chapter1.ch1DataProduction83 */},
_vo/* ch1DataProduction105 */ = new T2(3,_vn/* FormStructure.Chapter1.ch1DataProduction106 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_vp/* ch1DataProduction102 */ = new T1(1,_vi/* FormStructure.Chapter1.ch1DataProduction90 */),
_vq/* ch1DataProduction104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_vr/* ch1DataProduction103 */ = new T1(1,_vq/* FormStructure.Chapter1.ch1DataProduction104 */),
_vs/* ch1DataProduction101 */ = {_:0,a:_vr/* FormStructure.Chapter1.ch1DataProduction103 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_vp/* FormStructure.Chapter1.ch1DataProduction102 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_vm/* FormStructure.Chapter1.ch1DataProduction83 */},
_vt/* ch1DataProduction100 */ = new T2(3,_vs/* FormStructure.Chapter1.ch1DataProduction101 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_vu/* ch1DataProduction79 */ = new T1(1,_vd/* FormStructure.Chapter1.ch1DataProduction80 */),
_vv/* ch1DataProduction78 */ = {_:0,a:_ud/* FormStructure.Chapter1.ch1DataProduction27 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_vu/* FormStructure.Chapter1.ch1DataProduction79 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_u9/* FormStructure.Chapter1.ch1DataProduction21 */},
_vw/* ch1DataProduction77 */ = new T2(3,_vv/* FormStructure.Chapter1.ch1DataProduction78 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_vx/* ch1DataProduction76 */ = new T2(1,_vw/* FormStructure.Chapter1.ch1DataProduction77 */,_I/* GHC.Types.[] */),
_vy/* ch1DataProduction92 */ = new T1(1,_ve/* FormStructure.Chapter1.ch1DataProduction88 */),
_vz/* ch1DataProduction94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_vA/* ch1DataProduction93 */ = new T1(1,_vz/* FormStructure.Chapter1.ch1DataProduction94 */),
_vB/* ch1DataProduction82 */ = {_:0,a:_vA/* FormStructure.Chapter1.ch1DataProduction93 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_vy/* FormStructure.Chapter1.ch1DataProduction92 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_vm/* FormStructure.Chapter1.ch1DataProduction83 */},
_vC/* ch1DataProduction81 */ = new T2(3,_vB/* FormStructure.Chapter1.ch1DataProduction82 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_vD/* ch1DataProduction75 */ = new T2(1,_vC/* FormStructure.Chapter1.ch1DataProduction81 */,_vx/* FormStructure.Chapter1.ch1DataProduction76 */),
_vE/* ch1DataProduction97 */ = new T1(1,_vg/* FormStructure.Chapter1.ch1DataProduction89 */),
_vF/* ch1DataProduction99 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_vG/* ch1DataProduction98 */ = new T1(1,_vF/* FormStructure.Chapter1.ch1DataProduction99 */),
_vH/* ch1DataProduction96 */ = {_:0,a:_vG/* FormStructure.Chapter1.ch1DataProduction98 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_vE/* FormStructure.Chapter1.ch1DataProduction97 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_vm/* FormStructure.Chapter1.ch1DataProduction83 */},
_vI/* ch1DataProduction95 */ = new T2(3,_vH/* FormStructure.Chapter1.ch1DataProduction96 */,_u4/* FormStructure.Chapter1.ch1DataProduction18 */),
_vJ/* ch1DataProduction74 */ = new T2(1,_vI/* FormStructure.Chapter1.ch1DataProduction95 */,_vD/* FormStructure.Chapter1.ch1DataProduction75 */),
_vK/* ch1DataProduction73 */ = new T2(1,_vt/* FormStructure.Chapter1.ch1DataProduction100 */,_vJ/* FormStructure.Chapter1.ch1DataProduction74 */),
_vL/* ch1DataProduction72 */ = new T2(1,_vo/* FormStructure.Chapter1.ch1DataProduction105 */,_vK/* FormStructure.Chapter1.ch1DataProduction73 */),
_vM/* ch1DataProduction71 */ = new T3(8,_v8/* FormStructure.Chapter1.ch1DataProduction110 */,_tt/* FormStructure.Chapter1.ch1DataProduction67 */,_vL/* FormStructure.Chapter1.ch1DataProduction72 */),
_vN/* ch1DataProduction9 */ = new T2(1,_vM/* FormStructure.Chapter1.ch1DataProduction71 */,_v3/* FormStructure.Chapter1.ch1DataProduction10 */),
_vO/* ch1DataProduction8 */ = new T2(1,_u1/* FormStructure.Chapter1.ch1DataProduction115 */,_vN/* FormStructure.Chapter1.ch1DataProduction9 */),
_vP/* ch1DataProduction7 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_s1/* FormStructure.Chapter1.ch1DataProduction223 */,_vO/* FormStructure.Chapter1.ch1DataProduction8 */),
_vQ/* ch1DataProduction3 */ = new T2(1,_vP/* FormStructure.Chapter1.ch1DataProduction7 */,_s0/* FormStructure.Chapter1.ch1DataProduction4 */),
_vR/* ch1DataProduction2 */ = new T2(5,_rX/* FormStructure.Chapter1.ch1DataProduction224 */,_vQ/* FormStructure.Chapter1.ch1DataProduction3 */),
_vS/* ch1DataProduction1 */ = new T2(1,_vR/* FormStructure.Chapter1.ch1DataProduction2 */,_I/* GHC.Types.[] */),
_vT/* ch1DataProduction229 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("1.Production "));
}),
_vU/* ch1DataProduction228 */ = new T1(1,_vT/* FormStructure.Chapter1.ch1DataProduction229 */),
_vV/* ch1DataProduction227 */ = {_:0,a:_vU/* FormStructure.Chapter1.ch1DataProduction228 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_vW/* ch1DataProduction */ = new T2(7,_vV/* FormStructure.Chapter1.ch1DataProduction227 */,_vS/* FormStructure.Chapter1.ch1DataProduction1 */),
_vX/* ch2DataProcessing256 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you process raw data, i.e. you produce secondary data?"));
}),
_vY/* ch2DataProcessing255 */ = new T1(1,_vX/* FormStructure.Chapter2.ch2DataProcessing256 */),
_vZ/* ch2DataProcessing254 */ = {_:0,a:_vY/* FormStructure.Chapter2.ch2DataProcessing255 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_w0/* ch2DataProcessing6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_w1/* ch2DataProcessing5 */ = new T1(0,_w0/* FormStructure.Chapter2.ch2DataProcessing6 */),
_w2/* ch2DataProcessing4 */ = new T2(1,_w1/* FormStructure.Chapter2.ch2DataProcessing5 */,_I/* GHC.Types.[] */),
_w3/* ch2DataProcessing153 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_w4/* ch2DataProcessing152 */ = new T1(0,_w3/* FormStructure.Chapter2.ch2DataProcessing153 */),
_w5/* ch2DataProcessing156 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_w6/* ch2DataProcessing155 */ = new T1(1,_w5/* FormStructure.Chapter2.ch2DataProcessing156 */),
_w7/* ch2DataProcessing154 */ = {_:0,a:_w6/* FormStructure.Chapter2.ch2DataProcessing155 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_w8/* ch2DataProcessing151 */ = new T2(3,_w7/* FormStructure.Chapter2.ch2DataProcessing154 */,_w4/* FormStructure.Chapter2.ch2DataProcessing152 */),
_w9/* ch2DataProcessing150 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_wa/* ch2DataProcessing149 */ = new T1(1,_w9/* FormStructure.Chapter2.ch2DataProcessing150 */),
_wb/* ch2DataProcessing148 */ = {_:0,a:_wa/* FormStructure.Chapter2.ch2DataProcessing149 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_wc/* ch2DataProcessing21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_wd/* ch2DataProcessing20 */ = new T1(0,_wc/* FormStructure.Chapter2.ch2DataProcessing21 */),
_we/* ch2DataProcessing208 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-sum"));
}),
_wf/* ch2DataProcessing207 */ = new T1(1,_we/* FormStructure.Chapter2.ch2DataProcessing208 */),
_wg/* ch2DataProcessing26 */ = function(_wh/* sboJ */){
  return (E(_wh/* sboJ */)==100) ? true : false;
},
_wi/* ch2DataProcessing25 */ = new T1(4,_wg/* FormStructure.Chapter2.ch2DataProcessing26 */),
_wj/* ch2DataProcessing24 */ = new T2(1,_wi/* FormStructure.Chapter2.ch2DataProcessing25 */,_I/* GHC.Types.[] */),
_wk/* ch2DataProcessing23 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_wj/* FormStructure.Chapter2.ch2DataProcessing24 */),
_wl/* ch2DataProcessing30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_wm/* ch2DataProcessing29 */ = new T1(1,_wl/* FormStructure.Chapter2.ch2DataProcessing30 */),
_wn/* ch2DataProcessing206 */ = {_:0,a:_wm/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_wf/* FormStructure.Chapter2.ch2DataProcessing207 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wk/* FormStructure.Chapter2.ch2DataProcessing23 */},
_wo/* ch2DataProcessing205 */ = new T2(3,_wn/* FormStructure.Chapter2.ch2DataProcessing206 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wp/* ch2DataProcessing204 */ = new T2(1,_wo/* FormStructure.Chapter2.ch2DataProcessing205 */,_I/* GHC.Types.[] */),
_wq/* ch2DataProcessing132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_wr/* ch2DataProcessing131 */ = new T1(1,_wq/* FormStructure.Chapter2.ch2DataProcessing132 */),
_ws/* ch2DataProcessing36 */ = function(_wt/* sboD */){
  var _wu/* sboE */ = E(_wt/* sboD */);
  return (_wu/* sboE */<0) ? false : _wu/* sboE */<=100;
},
_wv/* ch2DataProcessing35 */ = new T1(4,_ws/* FormStructure.Chapter2.ch2DataProcessing36 */),
_ww/* ch2DataProcessing34 */ = new T2(1,_wv/* FormStructure.Chapter2.ch2DataProcessing35 */,_I/* GHC.Types.[] */),
_wx/* ch2DataProcessing216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-worldwide"));
}),
_wy/* ch2DataProcessing215 */ = new T2(1,_wx/* FormStructure.Chapter2.ch2DataProcessing216 */,_I/* GHC.Types.[] */),
_wz/* ch2DataProcessing217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-european"));
}),
_wA/* ch2DataProcessing214 */ = new T2(1,_wz/* FormStructure.Chapter2.ch2DataProcessing217 */,_wy/* FormStructure.Chapter2.ch2DataProcessing215 */),
_wB/* ch2DataProcessing218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-national"));
}),
_wC/* ch2DataProcessing213 */ = new T2(1,_wB/* FormStructure.Chapter2.ch2DataProcessing218 */,_wA/* FormStructure.Chapter2.ch2DataProcessing214 */),
_wD/* ch2DataProcessing219 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-external-internal-funding-institutional"));
}),
_wE/* ch2DataProcessing212 */ = new T2(1,_wD/* FormStructure.Chapter2.ch2DataProcessing219 */,_wC/* FormStructure.Chapter2.ch2DataProcessing213 */),
_wF/* ch2DataProcessing_fundingSumRule1 */ = new T2(0,_wE/* FormStructure.Chapter2.ch2DataProcessing212 */,_we/* FormStructure.Chapter2.ch2DataProcessing208 */),
_wG/* ch2DataProcessing211 */ = new T2(1,_wF/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule1 */,_ww/* FormStructure.Chapter2.ch2DataProcessing34 */),
_wH/* ch2DataProcessing220 */ = new T1(1,_wx/* FormStructure.Chapter2.ch2DataProcessing216 */),
_wI/* ch2DataProcessing210 */ = {_:0,a:_wr/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_wH/* FormStructure.Chapter2.ch2DataProcessing220 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wG/* FormStructure.Chapter2.ch2DataProcessing211 */},
_wJ/* ch2DataProcessing209 */ = new T2(3,_wI/* FormStructure.Chapter2.ch2DataProcessing210 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wK/* ch2DataProcessing203 */ = new T2(1,_wJ/* FormStructure.Chapter2.ch2DataProcessing209 */,_wp/* FormStructure.Chapter2.ch2DataProcessing204 */),
_wL/* ch2DataProcessing137 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_wM/* ch2DataProcessing136 */ = new T1(1,_wL/* FormStructure.Chapter2.ch2DataProcessing137 */),
_wN/* ch2DataProcessing223 */ = new T1(1,_wz/* FormStructure.Chapter2.ch2DataProcessing217 */),
_wO/* ch2DataProcessing222 */ = {_:0,a:_wM/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_wN/* FormStructure.Chapter2.ch2DataProcessing223 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wG/* FormStructure.Chapter2.ch2DataProcessing211 */},
_wP/* ch2DataProcessing221 */ = new T2(3,_wO/* FormStructure.Chapter2.ch2DataProcessing222 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wQ/* ch2DataProcessing202 */ = new T2(1,_wP/* FormStructure.Chapter2.ch2DataProcessing221 */,_wK/* FormStructure.Chapter2.ch2DataProcessing203 */),
_wR/* ch2DataProcessing142 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_wS/* ch2DataProcessing141 */ = new T1(1,_wR/* FormStructure.Chapter2.ch2DataProcessing142 */),
_wT/* ch2DataProcessing226 */ = new T1(1,_wB/* FormStructure.Chapter2.ch2DataProcessing218 */),
_wU/* ch2DataProcessing225 */ = {_:0,a:_wS/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_wT/* FormStructure.Chapter2.ch2DataProcessing226 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wG/* FormStructure.Chapter2.ch2DataProcessing211 */},
_wV/* ch2DataProcessing224 */ = new T2(3,_wU/* FormStructure.Chapter2.ch2DataProcessing225 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_wW/* ch2DataProcessing201 */ = new T2(1,_wV/* FormStructure.Chapter2.ch2DataProcessing224 */,_wQ/* FormStructure.Chapter2.ch2DataProcessing202 */),
_wX/* ch2DataProcessing147 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_wY/* ch2DataProcessing146 */ = new T1(1,_wX/* FormStructure.Chapter2.ch2DataProcessing147 */),
_wZ/* ch2DataProcessing229 */ = new T1(1,_wD/* FormStructure.Chapter2.ch2DataProcessing219 */),
_x0/* ch2DataProcessing228 */ = {_:0,a:_wY/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_wZ/* FormStructure.Chapter2.ch2DataProcessing229 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wG/* FormStructure.Chapter2.ch2DataProcessing211 */},
_x1/* ch2DataProcessing227 */ = new T2(3,_x0/* FormStructure.Chapter2.ch2DataProcessing228 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_x2/* ch2DataProcessing200 */ = new T2(1,_x1/* FormStructure.Chapter2.ch2DataProcessing227 */,_wW/* FormStructure.Chapter2.ch2DataProcessing201 */),
_x3/* ch2DataProcessing69 */ = 0,
_x4/* ch2DataProcessing199 */ = new T3(8,_wb/* FormStructure.Chapter2.ch2DataProcessing148 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_x2/* FormStructure.Chapter2.ch2DataProcessing200 */),
_x5/* ch2DataProcessing198 */ = new T2(1,_x4/* FormStructure.Chapter2.ch2DataProcessing199 */,_I/* GHC.Types.[] */),
_x6/* ch2DataProcessing197 */ = new T2(1,_w8/* FormStructure.Chapter2.ch2DataProcessing151 */,_x5/* FormStructure.Chapter2.ch2DataProcessing198 */),
_x7/* ch2DataProcessing232 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_x8/* ch2DataProcessing231 */ = new T1(1,_x7/* FormStructure.Chapter2.ch2DataProcessing232 */),
_x9/* ch2DataProcessing230 */ = {_:0,a:_x8/* FormStructure.Chapter2.ch2DataProcessing231 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xa/* ch2DataProcessing196 */ = new T3(8,_x9/* FormStructure.Chapter2.ch2DataProcessing230 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_x6/* FormStructure.Chapter2.ch2DataProcessing197 */),
_xb/* ch2DataProcessing195 */ = new T2(1,_xa/* FormStructure.Chapter2.ch2DataProcessing196 */,_I/* GHC.Types.[] */),
_xc/* ch2DataProcessing170 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_xd/* ch2DataProcessing169 */ = new T2(1,_xc/* FormStructure.Chapter2.ch2DataProcessing170 */,_I/* GHC.Types.[] */),
_xe/* ch2DataProcessing171 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_xf/* ch2DataProcessing168 */ = new T2(1,_xe/* FormStructure.Chapter2.ch2DataProcessing171 */,_xd/* FormStructure.Chapter2.ch2DataProcessing169 */),
_xg/* ch2DataProcessing172 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_xh/* ch2DataProcessing167 */ = new T2(1,_xg/* FormStructure.Chapter2.ch2DataProcessing172 */,_xf/* FormStructure.Chapter2.ch2DataProcessing168 */),
_xi/* ch2DataProcessing173 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_xj/* ch2DataProcessing166 */ = new T2(1,_xi/* FormStructure.Chapter2.ch2DataProcessing173 */,_xh/* FormStructure.Chapter2.ch2DataProcessing167 */),
_xk/* ch2DataProcessing165 */ = new T1(1,_xj/* FormStructure.Chapter2.ch2DataProcessing166 */),
_xl/* ch2DataProcessing236 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_xm/* ch2DataProcessing235 */ = new T1(1,_xl/* FormStructure.Chapter2.ch2DataProcessing236 */),
_xn/* ch2DataProcessing238 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_2"));
}),
_xo/* ch2DataProcessing237 */ = new T2(1,_xn/* FormStructure.Chapter2.ch2DataProcessing238 */,_I/* GHC.Types.[] */),
_xp/* ch2DataProcessing240 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific raw data volume"));
}),
_xq/* ch2DataProcessing239 */ = new T1(1,_xp/* FormStructure.Chapter2.ch2DataProcessing240 */),
_xr/* ch2DataProcessing234 */ = {_:0,a:_xq/* FormStructure.Chapter2.ch2DataProcessing239 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_xo/* FormStructure.Chapter2.ch2DataProcessing237 */,e:_xm/* FormStructure.Chapter2.ch2DataProcessing235 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xs/* ch2DataProcessing233 */ = new T2(3,_xr/* FormStructure.Chapter2.ch2DataProcessing234 */,_xk/* FormStructure.Chapter2.ch2DataProcessing165 */),
_xt/* ch2DataProcessing194 */ = new T2(1,_xs/* FormStructure.Chapter2.ch2DataProcessing233 */,_xb/* FormStructure.Chapter2.ch2DataProcessing195 */),
_xu/* ch2DataProcessing242 */ = new T1(0,_xe/* FormStructure.Chapter2.ch2DataProcessing171 */),
_xv/* ch2DataProcessing244 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_xw/* ch2DataProcessing246 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_xx/* ch2DataProcessing245 */ = new T2(1,_xw/* FormStructure.Chapter2.ch2DataProcessing246 */,_I/* GHC.Types.[] */),
_xy/* ch2DataProcessing248 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-raw-volume"));
}),
_xz/* ch2DataProcessing247 */ = new T1(1,_xy/* FormStructure.Chapter2.ch2DataProcessing248 */),
_xA/* ch2DataProcessing250 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_xB/* ch2DataProcessing249 */ = new T1(1,_xA/* FormStructure.Chapter2.ch2DataProcessing250 */),
_xC/* ch2DataProcessing243 */ = {_:0,a:_xB/* FormStructure.Chapter2.ch2DataProcessing249 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_xz/* FormStructure.Chapter2.ch2DataProcessing247 */,d:_xx/* FormStructure.Chapter2.ch2DataProcessing245 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_xv/* FormStructure.Chapter2.ch2DataProcessing244 */},
_xD/* ch2DataProcessing241 */ = new T2(3,_xC/* FormStructure.Chapter2.ch2DataProcessing243 */,_xu/* FormStructure.Chapter2.ch2DataProcessing242 */),
_xE/* ch2DataProcessing193 */ = new T2(1,_xD/* FormStructure.Chapter2.ch2DataProcessing241 */,_xt/* FormStructure.Chapter2.ch2DataProcessing194 */),
_xF/* ch2DataProcessing253 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_xG/* ch2DataProcessing252 */ = new T1(1,_xF/* FormStructure.Chapter2.ch2DataProcessing253 */),
_xH/* ch2DataProcessing251 */ = {_:0,a:_xG/* FormStructure.Chapter2.ch2DataProcessing252 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_xI/* ch2DataProcessing192 */ = new T3(8,_xH/* FormStructure.Chapter2.ch2DataProcessing251 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_xE/* FormStructure.Chapter2.ch2DataProcessing193 */),
_xJ/* ch2DataProcessing118 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-sum"));
}),
_xK/* ch2DataProcessing117 */ = new T1(1,_xJ/* FormStructure.Chapter2.ch2DataProcessing118 */),
_xL/* ch2DataProcessing116 */ = {_:0,a:_wm/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_xK/* FormStructure.Chapter2.ch2DataProcessing117 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wk/* FormStructure.Chapter2.ch2DataProcessing23 */},
_xM/* ch2DataProcessing115 */ = new T2(3,_xL/* FormStructure.Chapter2.ch2DataProcessing116 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_xN/* ch2DataProcessing114 */ = new T2(1,_xM/* FormStructure.Chapter2.ch2DataProcessing115 */,_I/* GHC.Types.[] */),
_xO/* ch2DataProcessing126 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-worldwide"));
}),
_xP/* ch2DataProcessing125 */ = new T2(1,_xO/* FormStructure.Chapter2.ch2DataProcessing126 */,_I/* GHC.Types.[] */),
_xQ/* ch2DataProcessing127 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-european"));
}),
_xR/* ch2DataProcessing124 */ = new T2(1,_xQ/* FormStructure.Chapter2.ch2DataProcessing127 */,_xP/* FormStructure.Chapter2.ch2DataProcessing125 */),
_xS/* ch2DataProcessing128 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-national"));
}),
_xT/* ch2DataProcessing123 */ = new T2(1,_xS/* FormStructure.Chapter2.ch2DataProcessing128 */,_xR/* FormStructure.Chapter2.ch2DataProcessing124 */),
_xU/* ch2DataProcessing129 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-internal-funding-institutional"));
}),
_xV/* ch2DataProcessing122 */ = new T2(1,_xU/* FormStructure.Chapter2.ch2DataProcessing129 */,_xT/* FormStructure.Chapter2.ch2DataProcessing123 */),
_xW/* ch2DataProcessing_fundingSumRule */ = new T2(0,_xV/* FormStructure.Chapter2.ch2DataProcessing122 */,_xJ/* FormStructure.Chapter2.ch2DataProcessing118 */),
_xX/* ch2DataProcessing121 */ = new T2(1,_xW/* FormStructure.Chapter2.ch2DataProcessing_fundingSumRule */,_ww/* FormStructure.Chapter2.ch2DataProcessing34 */),
_xY/* ch2DataProcessing130 */ = new T1(1,_xO/* FormStructure.Chapter2.ch2DataProcessing126 */),
_xZ/* ch2DataProcessing120 */ = {_:0,a:_wr/* FormStructure.Chapter2.ch2DataProcessing131 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_xY/* FormStructure.Chapter2.ch2DataProcessing130 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_xX/* FormStructure.Chapter2.ch2DataProcessing121 */},
_y0/* ch2DataProcessing119 */ = new T2(3,_xZ/* FormStructure.Chapter2.ch2DataProcessing120 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_y1/* ch2DataProcessing113 */ = new T2(1,_y0/* FormStructure.Chapter2.ch2DataProcessing119 */,_xN/* FormStructure.Chapter2.ch2DataProcessing114 */),
_y2/* ch2DataProcessing135 */ = new T1(1,_xQ/* FormStructure.Chapter2.ch2DataProcessing127 */),
_y3/* ch2DataProcessing134 */ = {_:0,a:_wM/* FormStructure.Chapter2.ch2DataProcessing136 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_y2/* FormStructure.Chapter2.ch2DataProcessing135 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_xX/* FormStructure.Chapter2.ch2DataProcessing121 */},
_y4/* ch2DataProcessing133 */ = new T2(3,_y3/* FormStructure.Chapter2.ch2DataProcessing134 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_y5/* ch2DataProcessing112 */ = new T2(1,_y4/* FormStructure.Chapter2.ch2DataProcessing133 */,_y1/* FormStructure.Chapter2.ch2DataProcessing113 */),
_y6/* ch2DataProcessing140 */ = new T1(1,_xS/* FormStructure.Chapter2.ch2DataProcessing128 */),
_y7/* ch2DataProcessing139 */ = {_:0,a:_wS/* FormStructure.Chapter2.ch2DataProcessing141 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_y6/* FormStructure.Chapter2.ch2DataProcessing140 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_xX/* FormStructure.Chapter2.ch2DataProcessing121 */},
_y8/* ch2DataProcessing138 */ = new T2(3,_y7/* FormStructure.Chapter2.ch2DataProcessing139 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_y9/* ch2DataProcessing111 */ = new T2(1,_y8/* FormStructure.Chapter2.ch2DataProcessing138 */,_y5/* FormStructure.Chapter2.ch2DataProcessing112 */),
_ya/* ch2DataProcessing145 */ = new T1(1,_xU/* FormStructure.Chapter2.ch2DataProcessing129 */),
_yb/* ch2DataProcessing144 */ = {_:0,a:_wY/* FormStructure.Chapter2.ch2DataProcessing146 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_ya/* FormStructure.Chapter2.ch2DataProcessing145 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_xX/* FormStructure.Chapter2.ch2DataProcessing121 */},
_yc/* ch2DataProcessing143 */ = new T2(3,_yb/* FormStructure.Chapter2.ch2DataProcessing144 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_yd/* ch2DataProcessing110 */ = new T2(1,_yc/* FormStructure.Chapter2.ch2DataProcessing143 */,_y9/* FormStructure.Chapter2.ch2DataProcessing111 */),
_ye/* ch2DataProcessing109 */ = new T3(8,_wb/* FormStructure.Chapter2.ch2DataProcessing148 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_yd/* FormStructure.Chapter2.ch2DataProcessing110 */),
_yf/* ch2DataProcessing108 */ = new T2(1,_ye/* FormStructure.Chapter2.ch2DataProcessing109 */,_I/* GHC.Types.[] */),
_yg/* ch2DataProcessing107 */ = new T2(1,_w8/* FormStructure.Chapter2.ch2DataProcessing151 */,_yf/* FormStructure.Chapter2.ch2DataProcessing108 */),
_yh/* ch2DataProcessing159 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_yi/* ch2DataProcessing158 */ = new T1(1,_yh/* FormStructure.Chapter2.ch2DataProcessing159 */),
_yj/* ch2DataProcessing161 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of data processing"));
}),
_yk/* ch2DataProcessing160 */ = new T1(1,_yj/* FormStructure.Chapter2.ch2DataProcessing161 */),
_yl/* ch2DataProcessing157 */ = {_:0,a:_yk/* FormStructure.Chapter2.ch2DataProcessing160 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_yi/* FormStructure.Chapter2.ch2DataProcessing158 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_ym/* ch2DataProcessing106 */ = new T3(8,_yl/* FormStructure.Chapter2.ch2DataProcessing157 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_yg/* FormStructure.Chapter2.ch2DataProcessing107 */),
_yn/* ch2DataProcessing13 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_yo/* ch2DataProcessing28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-sum"));
}),
_yp/* ch2DataProcessing27 */ = new T1(1,_yo/* FormStructure.Chapter2.ch2DataProcessing28 */),
_yq/* ch2DataProcessing22 */ = {_:0,a:_wm/* FormStructure.Chapter2.ch2DataProcessing29 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_yp/* FormStructure.Chapter2.ch2DataProcessing27 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_wk/* FormStructure.Chapter2.ch2DataProcessing23 */},
_yr/* ch2DataProcessing19 */ = new T2(3,_yq/* FormStructure.Chapter2.ch2DataProcessing22 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_ys/* ch2DataProcessing18 */ = new T2(1,_yr/* FormStructure.Chapter2.ch2DataProcessing19 */,_I/* GHC.Types.[] */),
_yt/* ch2DataProcessing40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-open"));
}),
_yu/* ch2DataProcessing39 */ = new T2(1,_yt/* FormStructure.Chapter2.ch2DataProcessing40 */,_I/* GHC.Types.[] */),
_yv/* ch2DataProcessing41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-closed"));
}),
_yw/* ch2DataProcessing38 */ = new T2(1,_yv/* FormStructure.Chapter2.ch2DataProcessing41 */,_yu/* FormStructure.Chapter2.ch2DataProcessing39 */),
_yx/* ch2DataProcessing42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-accessibility-inside"));
}),
_yy/* ch2DataProcessing37 */ = new T2(1,_yx/* FormStructure.Chapter2.ch2DataProcessing42 */,_yw/* FormStructure.Chapter2.ch2DataProcessing38 */),
_yz/* ch2DataProcessing_accSumRule */ = new T2(0,_yy/* FormStructure.Chapter2.ch2DataProcessing37 */,_yo/* FormStructure.Chapter2.ch2DataProcessing28 */),
_yA/* ch2DataProcessing33 */ = new T2(1,_yz/* FormStructure.Chapter2.ch2DataProcessing_accSumRule */,_ww/* FormStructure.Chapter2.ch2DataProcessing34 */),
_yB/* ch2DataProcessing44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_yC/* ch2DataProcessing43 */ = new T1(1,_yB/* FormStructure.Chapter2.ch2DataProcessing44 */),
_yD/* ch2DataProcessing47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_yE/* ch2DataProcessing46 */ = new T2(1,_yD/* FormStructure.Chapter2.ch2DataProcessing47 */,_I/* GHC.Types.[] */),
_yF/* ch2DataProcessing48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_yG/* ch2DataProcessing45 */ = new T2(1,_yF/* FormStructure.Chapter2.ch2DataProcessing48 */,_yE/* FormStructure.Chapter2.ch2DataProcessing46 */),
_yH/* ch2DataProcessing49 */ = new T1(1,_yt/* FormStructure.Chapter2.ch2DataProcessing40 */),
_yI/* ch2DataProcessing51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_yJ/* ch2DataProcessing50 */ = new T1(1,_yI/* FormStructure.Chapter2.ch2DataProcessing51 */),
_yK/* ch2DataProcessing32 */ = {_:0,a:_yJ/* FormStructure.Chapter2.ch2DataProcessing50 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_yH/* FormStructure.Chapter2.ch2DataProcessing49 */,d:_yG/* FormStructure.Chapter2.ch2DataProcessing45 */,e:_yC/* FormStructure.Chapter2.ch2DataProcessing43 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_yA/* FormStructure.Chapter2.ch2DataProcessing33 */},
_yL/* ch2DataProcessing31 */ = new T2(3,_yK/* FormStructure.Chapter2.ch2DataProcessing32 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_yM/* ch2DataProcessing17 */ = new T2(1,_yL/* FormStructure.Chapter2.ch2DataProcessing31 */,_ys/* FormStructure.Chapter2.ch2DataProcessing18 */),
_yN/* ch2DataProcessing55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_yO/* ch2DataProcessing54 */ = new T1(1,_yN/* FormStructure.Chapter2.ch2DataProcessing55 */),
_yP/* ch2DataProcessing58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_yQ/* ch2DataProcessing57 */ = new T2(1,_yP/* FormStructure.Chapter2.ch2DataProcessing58 */,_I/* GHC.Types.[] */),
_yR/* ch2DataProcessing56 */ = new T2(1,_yF/* FormStructure.Chapter2.ch2DataProcessing48 */,_yQ/* FormStructure.Chapter2.ch2DataProcessing57 */),
_yS/* ch2DataProcessing59 */ = new T1(1,_yv/* FormStructure.Chapter2.ch2DataProcessing41 */),
_yT/* ch2DataProcessing61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_yU/* ch2DataProcessing60 */ = new T1(1,_yT/* FormStructure.Chapter2.ch2DataProcessing61 */),
_yV/* ch2DataProcessing53 */ = {_:0,a:_yU/* FormStructure.Chapter2.ch2DataProcessing60 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_yS/* FormStructure.Chapter2.ch2DataProcessing59 */,d:_yR/* FormStructure.Chapter2.ch2DataProcessing56 */,e:_yO/* FormStructure.Chapter2.ch2DataProcessing54 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_yA/* FormStructure.Chapter2.ch2DataProcessing33 */},
_yW/* ch2DataProcessing52 */ = new T2(3,_yV/* FormStructure.Chapter2.ch2DataProcessing53 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_yX/* ch2DataProcessing16 */ = new T2(1,_yW/* FormStructure.Chapter2.ch2DataProcessing52 */,_yM/* FormStructure.Chapter2.ch2DataProcessing17 */),
_yY/* ch2DataProcessing65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_yZ/* ch2DataProcessing64 */ = new T2(1,_yY/* FormStructure.Chapter2.ch2DataProcessing65 */,_I/* GHC.Types.[] */),
_z0/* ch2DataProcessing66 */ = new T1(1,_yx/* FormStructure.Chapter2.ch2DataProcessing42 */),
_z1/* ch2DataProcessing68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_z2/* ch2DataProcessing67 */ = new T1(1,_z1/* FormStructure.Chapter2.ch2DataProcessing68 */),
_z3/* ch2DataProcessing63 */ = {_:0,a:_z2/* FormStructure.Chapter2.ch2DataProcessing67 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_z0/* FormStructure.Chapter2.ch2DataProcessing66 */,d:_yZ/* FormStructure.Chapter2.ch2DataProcessing64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_yA/* FormStructure.Chapter2.ch2DataProcessing33 */},
_z4/* ch2DataProcessing62 */ = new T2(3,_z3/* FormStructure.Chapter2.ch2DataProcessing63 */,_wd/* FormStructure.Chapter2.ch2DataProcessing20 */),
_z5/* ch2DataProcessing15 */ = new T2(1,_z4/* FormStructure.Chapter2.ch2DataProcessing62 */,_yX/* FormStructure.Chapter2.ch2DataProcessing16 */),
_z6/* ch2DataProcessing72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_z7/* ch2DataProcessing71 */ = new T1(1,_z6/* FormStructure.Chapter2.ch2DataProcessing72 */),
_z8/* ch2DataProcessing70 */ = {_:0,a:_z7/* FormStructure.Chapter2.ch2DataProcessing71 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_z9/* ch2DataProcessing14 */ = new T3(8,_z8/* FormStructure.Chapter2.ch2DataProcessing70 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_z5/* FormStructure.Chapter2.ch2DataProcessing15 */),
_za/* ch2DataProcessing12 */ = new T2(1,_z9/* FormStructure.Chapter2.ch2DataProcessing14 */,_yn/* FormStructure.Chapter2.ch2DataProcessing13 */),
_zb/* ch2DataProcessing103 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_zc/* ch2DataProcessing102 */ = new T1(1,_zb/* FormStructure.Chapter2.ch2DataProcessing103 */),
_zd/* ch2DataProcessing105 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_ze/* ch2DataProcessing104 */ = new T1(1,_zd/* FormStructure.Chapter2.ch2DataProcessing105 */),
_zf/* ch2DataProcessing101 */ = {_:0,a:_ze/* FormStructure.Chapter2.ch2DataProcessing104 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_zc/* FormStructure.Chapter2.ch2DataProcessing102 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_zg/* ch2DataProcessing82 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_zh/* ch2DataProcessing81 */ = new T1(0,_zg/* FormStructure.Chapter2.ch2DataProcessing82 */),
_zi/* ch2DataProcessing80 */ = new T2(1,_zh/* FormStructure.Chapter2.ch2DataProcessing81 */,_I/* GHC.Types.[] */),
_zj/* ch2DataProcessing84 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_zk/* ch2DataProcessing83 */ = new T1(0,_zj/* FormStructure.Chapter2.ch2DataProcessing84 */),
_zl/* ch2DataProcessing79 */ = new T2(1,_zk/* FormStructure.Chapter2.ch2DataProcessing83 */,_zi/* FormStructure.Chapter2.ch2DataProcessing80 */),
_zm/* ch2DataProcessing86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_zn/* ch2DataProcessing85 */ = new T1(0,_zm/* FormStructure.Chapter2.ch2DataProcessing86 */),
_zo/* ch2DataProcessing78 */ = new T2(1,_zn/* FormStructure.Chapter2.ch2DataProcessing85 */,_zl/* FormStructure.Chapter2.ch2DataProcessing79 */),
_zp/* ch2DataProcessing88 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_zq/* ch2DataProcessing87 */ = new T1(0,_zp/* FormStructure.Chapter2.ch2DataProcessing88 */),
_zr/* ch2DataProcessing77 */ = new T2(1,_zq/* FormStructure.Chapter2.ch2DataProcessing87 */,_zo/* FormStructure.Chapter2.ch2DataProcessing78 */),
_zs/* ch2DataProcessing91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_zt/* ch2DataProcessing90 */ = new T1(1,_zs/* FormStructure.Chapter2.ch2DataProcessing91 */),
_zu/* ch2DataProcessing93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_zv/* ch2DataProcessing92 */ = new T1(1,_zu/* FormStructure.Chapter2.ch2DataProcessing93 */),
_zw/* ch2DataProcessing89 */ = {_:0,a:_zv/* FormStructure.Chapter2.ch2DataProcessing92 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_zt/* FormStructure.Chapter2.ch2DataProcessing90 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_zx/* ch2DataProcessing76 */ = new T2(5,_zw/* FormStructure.Chapter2.ch2DataProcessing89 */,_zr/* FormStructure.Chapter2.ch2DataProcessing77 */),
_zy/* ch2DataProcessing75 */ = new T2(1,_zx/* FormStructure.Chapter2.ch2DataProcessing76 */,_I/* GHC.Types.[] */),
_zz/* ch2DataProcessing97 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_zA/* ch2DataProcessing96 */ = new T1(0,_zz/* FormStructure.Chapter2.ch2DataProcessing97 */),
_zB/* ch2DataProcessing95 */ = new T2(1,_zA/* FormStructure.Chapter2.ch2DataProcessing96 */,_w2/* FormStructure.Chapter2.ch2DataProcessing4 */),
_zC/* ch2DataProcessing100 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_zD/* ch2DataProcessing99 */ = new T1(1,_zC/* FormStructure.Chapter2.ch2DataProcessing100 */),
_zE/* ch2DataProcessing98 */ = {_:0,a:_zD/* FormStructure.Chapter2.ch2DataProcessing99 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_zF/* ch2DataProcessing94 */ = new T2(5,_zE/* FormStructure.Chapter2.ch2DataProcessing98 */,_zB/* FormStructure.Chapter2.ch2DataProcessing95 */),
_zG/* ch2DataProcessing74 */ = new T2(1,_zF/* FormStructure.Chapter2.ch2DataProcessing94 */,_zy/* FormStructure.Chapter2.ch2DataProcessing75 */),
_zH/* ch2DataProcessing73 */ = new T3(8,_zf/* FormStructure.Chapter2.ch2DataProcessing101 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_zG/* FormStructure.Chapter2.ch2DataProcessing74 */),
_zI/* ch2DataProcessing11 */ = new T2(1,_zH/* FormStructure.Chapter2.ch2DataProcessing73 */,_za/* FormStructure.Chapter2.ch2DataProcessing12 */),
_zJ/* ch2DataProcessing10 */ = new T2(1,_ym/* FormStructure.Chapter2.ch2DataProcessing106 */,_zI/* FormStructure.Chapter2.ch2DataProcessing11 */),
_zK/* ch2DataProcessing176 */ = new T2(1,_sq/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_zL/* ch2DataProcessing178 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_zM/* ch2DataProcessing179 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("prim-volume"));
}),
_zN/* ch2DataProcessing177 */ = new T2(2,_zM/* FormStructure.Chapter2.ch2DataProcessing179 */,_zL/* FormStructure.Chapter2.ch2DataProcessing178 */),
_zO/* ch2DataProcessing175 */ = new T2(1,_zN/* FormStructure.Chapter2.ch2DataProcessing177 */,_zK/* FormStructure.Chapter2.ch2DataProcessing176 */),
_zP/* ch2DataProcessing181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_zQ/* ch2DataProcessing180 */ = new T1(1,_zP/* FormStructure.Chapter2.ch2DataProcessing181 */),
_zR/* ch2DataProcessing184 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_zS/* ch2DataProcessing183 */ = new T2(1,_zR/* FormStructure.Chapter2.ch2DataProcessing184 */,_I/* GHC.Types.[] */),
_zT/* ch2DataProcessing185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_zU/* ch2DataProcessing182 */ = new T2(1,_zT/* FormStructure.Chapter2.ch2DataProcessing185 */,_zS/* FormStructure.Chapter2.ch2DataProcessing183 */),
_zV/* ch2DataProcessing186 */ = new T1(1,_zM/* FormStructure.Chapter2.ch2DataProcessing179 */),
_zW/* ch2DataProcessing188 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_zX/* ch2DataProcessing187 */ = new T1(1,_zW/* FormStructure.Chapter2.ch2DataProcessing188 */),
_zY/* ch2DataProcessing174 */ = {_:0,a:_zX/* FormStructure.Chapter2.ch2DataProcessing187 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_zV/* FormStructure.Chapter2.ch2DataProcessing186 */,d:_zU/* FormStructure.Chapter2.ch2DataProcessing182 */,e:_zQ/* FormStructure.Chapter2.ch2DataProcessing180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_zO/* FormStructure.Chapter2.ch2DataProcessing175 */},
_zZ/* ch2DataProcessing164 */ = new T2(3,_zY/* FormStructure.Chapter2.ch2DataProcessing174 */,_xk/* FormStructure.Chapter2.ch2DataProcessing165 */),
_A0/* ch2DataProcessing163 */ = new T2(1,_zZ/* FormStructure.Chapter2.ch2DataProcessing164 */,_I/* GHC.Types.[] */),
_A1/* ch2DataProcessing191 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_A2/* ch2DataProcessing190 */ = new T1(1,_A1/* FormStructure.Chapter2.ch2DataProcessing191 */),
_A3/* ch2DataProcessing189 */ = {_:0,a:_A2/* FormStructure.Chapter2.ch2DataProcessing190 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_A4/* ch2DataProcessing162 */ = new T3(8,_A3/* FormStructure.Chapter2.ch2DataProcessing189 */,_x3/* FormStructure.Chapter2.ch2DataProcessing69 */,_A0/* FormStructure.Chapter2.ch2DataProcessing163 */),
_A5/* ch2DataProcessing9 */ = new T2(1,_A4/* FormStructure.Chapter2.ch2DataProcessing162 */,_zJ/* FormStructure.Chapter2.ch2DataProcessing10 */),
_A6/* ch2DataProcessing8 */ = new T2(1,_xI/* FormStructure.Chapter2.ch2DataProcessing192 */,_A5/* FormStructure.Chapter2.ch2DataProcessing9 */),
_A7/* ch2DataProcessing7 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_zz/* FormStructure.Chapter2.ch2DataProcessing97 */,_A6/* FormStructure.Chapter2.ch2DataProcessing8 */),
_A8/* ch2DataProcessing3 */ = new T2(1,_A7/* FormStructure.Chapter2.ch2DataProcessing7 */,_w2/* FormStructure.Chapter2.ch2DataProcessing4 */),
_A9/* ch2DataProcessing2 */ = new T2(5,_vZ/* FormStructure.Chapter2.ch2DataProcessing254 */,_A8/* FormStructure.Chapter2.ch2DataProcessing3 */),
_Aa/* ch2DataProcessing1 */ = new T2(1,_A9/* FormStructure.Chapter2.ch2DataProcessing2 */,_I/* GHC.Types.[] */),
_Ab/* ch2DataProcessing259 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("2.Processing "));
}),
_Ac/* ch2DataProcessing258 */ = new T1(1,_Ab/* FormStructure.Chapter2.ch2DataProcessing259 */),
_Ad/* ch2DataProcessing257 */ = {_:0,a:_Ac/* FormStructure.Chapter2.ch2DataProcessing258 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ae/* ch2DataProcessing */ = new T2(7,_Ad/* FormStructure.Chapter2.ch2DataProcessing257 */,_Aa/* FormStructure.Chapter2.ch2DataProcessing1 */),
_Af/* ch3DataUsage264 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you use data, i.e. to perform analyses?"));
}),
_Ag/* ch3DataUsage263 */ = new T1(1,_Af/* FormStructure.Chapter3.ch3DataUsage264 */),
_Ah/* ch3DataUsage262 */ = {_:0,a:_Ag/* FormStructure.Chapter3.ch3DataUsage263 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ai/* ch3DataUsage6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_Aj/* ch3DataUsage5 */ = new T1(0,_Ai/* FormStructure.Chapter3.ch3DataUsage6 */),
_Ak/* ch3DataUsage4 */ = new T2(1,_Aj/* FormStructure.Chapter3.ch3DataUsage5 */,_I/* GHC.Types.[] */),
_Al/* ch3DataUsage258 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("A typical usage is performing a certain analysis."));
}),
_Am/* ch3DataUsage257 */ = new T1(1,_Al/* FormStructure.Chapter3.ch3DataUsage258 */),
_An/* ch3DataUsage260 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Describe the usage"));
}),
_Ao/* ch3DataUsage259 */ = new T1(1,_An/* FormStructure.Chapter3.ch3DataUsage260 */),
_Ap/* ch3DataUsage256 */ = {_:0,a:_Ao/* FormStructure.Chapter3.ch3DataUsage259 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_Am/* FormStructure.Chapter3.ch3DataUsage257 */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Aq/* ch3DataUsage255 */ = new T1(1,_Ap/* FormStructure.Chapter3.ch3DataUsage256 */),
_Ar/* ch3DataUsage254 */ = new T2(1,_Aq/* FormStructure.Chapter3.ch3DataUsage255 */,_I/* GHC.Types.[] */),
_As/* ch3DataUsage261 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_At/* ch3DataUsage70 */ = 0,
_Au/* ch3DataUsage253 */ = new T3(8,_As/* FormStructure.Chapter3.ch3DataUsage261 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Ar/* FormStructure.Chapter3.ch3DataUsage254 */),
_Av/* ch3DataUsage119 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-sum"));
}),
_Aw/* ch3DataUsage118 */ = new T1(1,_Av/* FormStructure.Chapter3.ch3DataUsage119 */),
_Ax/* ch3DataUsage27 */ = function(_Ay/* sctr */){
  return (E(_Ay/* sctr */)==100) ? true : false;
},
_Az/* ch3DataUsage26 */ = new T1(4,_Ax/* FormStructure.Chapter3.ch3DataUsage27 */),
_AA/* ch3DataUsage25 */ = new T2(1,_Az/* FormStructure.Chapter3.ch3DataUsage26 */,_I/* GHC.Types.[] */),
_AB/* ch3DataUsage24 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_AA/* FormStructure.Chapter3.ch3DataUsage25 */),
_AC/* ch3DataUsage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_AD/* ch3DataUsage30 */ = new T1(1,_AC/* FormStructure.Chapter3.ch3DataUsage31 */),
_AE/* ch3DataUsage117 */ = {_:0,a:_AD/* FormStructure.Chapter3.ch3DataUsage30 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Aw/* FormStructure.Chapter3.ch3DataUsage118 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AB/* FormStructure.Chapter3.ch3DataUsage24 */},
_AF/* ch3DataUsage22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_AG/* ch3DataUsage21 */ = new T1(0,_AF/* FormStructure.Chapter3.ch3DataUsage22 */),
_AH/* ch3DataUsage116 */ = new T2(3,_AE/* FormStructure.Chapter3.ch3DataUsage117 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_AI/* ch3DataUsage115 */ = new T2(1,_AH/* FormStructure.Chapter3.ch3DataUsage116 */,_I/* GHC.Types.[] */),
_AJ/* ch3DataUsage125 */ = function(_AK/* sctl */){
  var _AL/* sctm */ = E(_AK/* sctl */);
  return (_AL/* sctm */<0) ? false : _AL/* sctm */<=100;
},
_AM/* ch3DataUsage124 */ = new T1(4,_AJ/* FormStructure.Chapter3.ch3DataUsage125 */),
_AN/* ch3DataUsage123 */ = new T2(1,_AM/* FormStructure.Chapter3.ch3DataUsage124 */,_I/* GHC.Types.[] */),
_AO/* ch3DataUsage130 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-worldwide"));
}),
_AP/* ch3DataUsage129 */ = new T2(1,_AO/* FormStructure.Chapter3.ch3DataUsage130 */,_I/* GHC.Types.[] */),
_AQ/* ch3DataUsage131 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-european"));
}),
_AR/* ch3DataUsage128 */ = new T2(1,_AQ/* FormStructure.Chapter3.ch3DataUsage131 */,_AP/* FormStructure.Chapter3.ch3DataUsage129 */),
_AS/* ch3DataUsage132 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-national"));
}),
_AT/* ch3DataUsage127 */ = new T2(1,_AS/* FormStructure.Chapter3.ch3DataUsage132 */,_AR/* FormStructure.Chapter3.ch3DataUsage128 */),
_AU/* ch3DataUsage133 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-internal-funding-institutional"));
}),
_AV/* ch3DataUsage126 */ = new T2(1,_AU/* FormStructure.Chapter3.ch3DataUsage133 */,_AT/* FormStructure.Chapter3.ch3DataUsage127 */),
_AW/* ch3DataUsage_fundingSumRule */ = new T2(0,_AV/* FormStructure.Chapter3.ch3DataUsage126 */,_Av/* FormStructure.Chapter3.ch3DataUsage119 */),
_AX/* ch3DataUsage122 */ = new T2(1,_AW/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule */,_AN/* FormStructure.Chapter3.ch3DataUsage123 */),
_AY/* ch3DataUsage134 */ = new T1(1,_AO/* FormStructure.Chapter3.ch3DataUsage130 */),
_AZ/* ch3DataUsage136 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("World-wide"));
}),
_B0/* ch3DataUsage135 */ = new T1(1,_AZ/* FormStructure.Chapter3.ch3DataUsage136 */),
_B1/* ch3DataUsage121 */ = {_:0,a:_B0/* FormStructure.Chapter3.ch3DataUsage135 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_AY/* FormStructure.Chapter3.ch3DataUsage134 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AX/* FormStructure.Chapter3.ch3DataUsage122 */},
_B2/* ch3DataUsage120 */ = new T2(3,_B1/* FormStructure.Chapter3.ch3DataUsage121 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_B3/* ch3DataUsage114 */ = new T2(1,_B2/* FormStructure.Chapter3.ch3DataUsage120 */,_AI/* FormStructure.Chapter3.ch3DataUsage115 */),
_B4/* ch3DataUsage139 */ = new T1(1,_AQ/* FormStructure.Chapter3.ch3DataUsage131 */),
_B5/* ch3DataUsage141 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("European"));
}),
_B6/* ch3DataUsage140 */ = new T1(1,_B5/* FormStructure.Chapter3.ch3DataUsage141 */),
_B7/* ch3DataUsage138 */ = {_:0,a:_B6/* FormStructure.Chapter3.ch3DataUsage140 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_B4/* FormStructure.Chapter3.ch3DataUsage139 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AX/* FormStructure.Chapter3.ch3DataUsage122 */},
_B8/* ch3DataUsage137 */ = new T2(3,_B7/* FormStructure.Chapter3.ch3DataUsage138 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_B9/* ch3DataUsage113 */ = new T2(1,_B8/* FormStructure.Chapter3.ch3DataUsage137 */,_B3/* FormStructure.Chapter3.ch3DataUsage114 */),
_Ba/* ch3DataUsage144 */ = new T1(1,_AS/* FormStructure.Chapter3.ch3DataUsage132 */),
_Bb/* ch3DataUsage146 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("National"));
}),
_Bc/* ch3DataUsage145 */ = new T1(1,_Bb/* FormStructure.Chapter3.ch3DataUsage146 */),
_Bd/* ch3DataUsage143 */ = {_:0,a:_Bc/* FormStructure.Chapter3.ch3DataUsage145 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Ba/* FormStructure.Chapter3.ch3DataUsage144 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AX/* FormStructure.Chapter3.ch3DataUsage122 */},
_Be/* ch3DataUsage142 */ = new T2(3,_Bd/* FormStructure.Chapter3.ch3DataUsage143 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bf/* ch3DataUsage112 */ = new T2(1,_Be/* FormStructure.Chapter3.ch3DataUsage142 */,_B9/* FormStructure.Chapter3.ch3DataUsage113 */),
_Bg/* ch3DataUsage149 */ = new T1(1,_AU/* FormStructure.Chapter3.ch3DataUsage133 */),
_Bh/* ch3DataUsage151 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_Bi/* ch3DataUsage150 */ = new T1(1,_Bh/* FormStructure.Chapter3.ch3DataUsage151 */),
_Bj/* ch3DataUsage148 */ = {_:0,a:_Bi/* FormStructure.Chapter3.ch3DataUsage150 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Bg/* FormStructure.Chapter3.ch3DataUsage149 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AX/* FormStructure.Chapter3.ch3DataUsage122 */},
_Bk/* ch3DataUsage147 */ = new T2(3,_Bj/* FormStructure.Chapter3.ch3DataUsage148 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_Bl/* ch3DataUsage111 */ = new T2(1,_Bk/* FormStructure.Chapter3.ch3DataUsage147 */,_Bf/* FormStructure.Chapter3.ch3DataUsage112 */),
_Bm/* ch3DataUsage154 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Funding"));
}),
_Bn/* ch3DataUsage153 */ = new T1(1,_Bm/* FormStructure.Chapter3.ch3DataUsage154 */),
_Bo/* ch3DataUsage152 */ = {_:0,a:_Bn/* FormStructure.Chapter3.ch3DataUsage153 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Bp/* ch3DataUsage110 */ = new T3(8,_Bo/* FormStructure.Chapter3.ch3DataUsage152 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Bl/* FormStructure.Chapter3.ch3DataUsage111 */),
_Bq/* ch3DataUsage109 */ = new T2(1,_Bp/* FormStructure.Chapter3.ch3DataUsage110 */,_I/* GHC.Types.[] */),
_Br/* ch3DataUsage157 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_Bs/* ch3DataUsage156 */ = new T1(0,_Br/* FormStructure.Chapter3.ch3DataUsage157 */),
_Bt/* ch3DataUsage160 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_Bu/* ch3DataUsage159 */ = new T1(1,_Bt/* FormStructure.Chapter3.ch3DataUsage160 */),
_Bv/* ch3DataUsage158 */ = {_:0,a:_Bu/* FormStructure.Chapter3.ch3DataUsage159 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Bw/* ch3DataUsage155 */ = new T2(3,_Bv/* FormStructure.Chapter3.ch3DataUsage158 */,_Bs/* FormStructure.Chapter3.ch3DataUsage156 */),
_Bx/* ch3DataUsage108 */ = new T2(1,_Bw/* FormStructure.Chapter3.ch3DataUsage155 */,_Bq/* FormStructure.Chapter3.ch3DataUsage109 */),
_By/* ch3DataUsage163 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rough estimation of FTEs + investments + consumables"));
}),
_Bz/* ch3DataUsage162 */ = new T1(1,_By/* FormStructure.Chapter3.ch3DataUsage163 */),
_BA/* ch3DataUsage165 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of secondary data production"));
}),
_BB/* ch3DataUsage164 */ = new T1(1,_BA/* FormStructure.Chapter3.ch3DataUsage165 */),
_BC/* ch3DataUsage161 */ = {_:0,a:_BB/* FormStructure.Chapter3.ch3DataUsage164 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Bz/* FormStructure.Chapter3.ch3DataUsage162 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_BD/* ch3DataUsage107 */ = new T3(8,_BC/* FormStructure.Chapter3.ch3DataUsage161 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Bx/* FormStructure.Chapter3.ch3DataUsage108 */),
_BE/* ch3DataUsage14 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_BF/* ch3DataUsage29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-sum"));
}),
_BG/* ch3DataUsage28 */ = new T1(1,_BF/* FormStructure.Chapter3.ch3DataUsage29 */),
_BH/* ch3DataUsage23 */ = {_:0,a:_AD/* FormStructure.Chapter3.ch3DataUsage30 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_BG/* FormStructure.Chapter3.ch3DataUsage28 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AB/* FormStructure.Chapter3.ch3DataUsage24 */},
_BI/* ch3DataUsage20 */ = new T2(3,_BH/* FormStructure.Chapter3.ch3DataUsage23 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_BJ/* ch3DataUsage19 */ = new T2(1,_BI/* FormStructure.Chapter3.ch3DataUsage20 */,_I/* GHC.Types.[] */),
_BK/* ch3DataUsage37 */ = function(_BL/* sctv */){
  return E(_BL/* sctv */)<=100;
},
_BM/* ch3DataUsage36 */ = new T1(4,_BK/* FormStructure.Chapter3.ch3DataUsage37 */),
_BN/* ch3DataUsage35 */ = new T2(1,_BM/* FormStructure.Chapter3.ch3DataUsage36 */,_I/* GHC.Types.[] */),
_BO/* ch3DataUsage41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-open"));
}),
_BP/* ch3DataUsage40 */ = new T2(1,_BO/* FormStructure.Chapter3.ch3DataUsage41 */,_I/* GHC.Types.[] */),
_BQ/* ch3DataUsage42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-closed"));
}),
_BR/* ch3DataUsage39 */ = new T2(1,_BQ/* FormStructure.Chapter3.ch3DataUsage42 */,_BP/* FormStructure.Chapter3.ch3DataUsage40 */),
_BS/* ch3DataUsage43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-accessibility-inside"));
}),
_BT/* ch3DataUsage38 */ = new T2(1,_BS/* FormStructure.Chapter3.ch3DataUsage43 */,_BR/* FormStructure.Chapter3.ch3DataUsage39 */),
_BU/* ch3DataUsage_accSumRule */ = new T2(0,_BT/* FormStructure.Chapter3.ch3DataUsage38 */,_BF/* FormStructure.Chapter3.ch3DataUsage29 */),
_BV/* ch3DataUsage34 */ = new T2(1,_BU/* FormStructure.Chapter3.ch3DataUsage_accSumRule */,_BN/* FormStructure.Chapter3.ch3DataUsage35 */),
_BW/* ch3DataUsage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Free or paid"));
}),
_BX/* ch3DataUsage44 */ = new T1(1,_BW/* FormStructure.Chapter3.ch3DataUsage45 */),
_BY/* ch3DataUsage48 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_oa"));
}),
_BZ/* ch3DataUsage47 */ = new T2(1,_BY/* FormStructure.Chapter3.ch3DataUsage48 */,_I/* GHC.Types.[] */),
_C0/* ch3DataUsage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_C1/* ch3DataUsage46 */ = new T2(1,_C0/* FormStructure.Chapter3.ch3DataUsage49 */,_BZ/* FormStructure.Chapter3.ch3DataUsage47 */),
_C2/* ch3DataUsage50 */ = new T1(1,_BO/* FormStructure.Chapter3.ch3DataUsage41 */),
_C3/* ch3DataUsage52 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External open access"));
}),
_C4/* ch3DataUsage51 */ = new T1(1,_C3/* FormStructure.Chapter3.ch3DataUsage52 */),
_C5/* ch3DataUsage33 */ = {_:0,a:_C4/* FormStructure.Chapter3.ch3DataUsage51 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_C2/* FormStructure.Chapter3.ch3DataUsage50 */,d:_C1/* FormStructure.Chapter3.ch3DataUsage46 */,e:_BX/* FormStructure.Chapter3.ch3DataUsage44 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_BV/* FormStructure.Chapter3.ch3DataUsage34 */},
_C6/* ch3DataUsage32 */ = new T2(3,_C5/* FormStructure.Chapter3.ch3DataUsage33 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_C7/* ch3DataUsage18 */ = new T2(1,_C6/* FormStructure.Chapter3.ch3DataUsage32 */,_BJ/* FormStructure.Chapter3.ch3DataUsage19 */),
_C8/* ch3DataUsage56 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("E.g. based on contract"));
}),
_C9/* ch3DataUsage55 */ = new T1(1,_C8/* FormStructure.Chapter3.ch3DataUsage56 */),
_Ca/* ch3DataUsage59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_5_ca"));
}),
_Cb/* ch3DataUsage58 */ = new T2(1,_Ca/* FormStructure.Chapter3.ch3DataUsage59 */,_I/* GHC.Types.[] */),
_Cc/* ch3DataUsage57 */ = new T2(1,_C0/* FormStructure.Chapter3.ch3DataUsage49 */,_Cb/* FormStructure.Chapter3.ch3DataUsage58 */),
_Cd/* ch3DataUsage60 */ = new T1(1,_BQ/* FormStructure.Chapter3.ch3DataUsage42 */),
_Ce/* ch3DataUsage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External closed access"));
}),
_Cf/* ch3DataUsage61 */ = new T1(1,_Ce/* FormStructure.Chapter3.ch3DataUsage62 */),
_Cg/* ch3DataUsage54 */ = {_:0,a:_Cf/* FormStructure.Chapter3.ch3DataUsage61 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Cd/* FormStructure.Chapter3.ch3DataUsage60 */,d:_Cc/* FormStructure.Chapter3.ch3DataUsage57 */,e:_C9/* FormStructure.Chapter3.ch3DataUsage55 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_BV/* FormStructure.Chapter3.ch3DataUsage34 */},
_Ch/* ch3DataUsage53 */ = new T2(3,_Cg/* FormStructure.Chapter3.ch3DataUsage54 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_Ci/* ch3DataUsage17 */ = new T2(1,_Ch/* FormStructure.Chapter3.ch3DataUsage53 */,_C7/* FormStructure.Chapter3.ch3DataUsage18 */),
_Cj/* ch3DataUsage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_Ck/* ch3DataUsage65 */ = new T2(1,_Cj/* FormStructure.Chapter3.ch3DataUsage66 */,_I/* GHC.Types.[] */),
_Cl/* ch3DataUsage67 */ = new T1(1,_BS/* FormStructure.Chapter3.ch3DataUsage43 */),
_Cm/* ch3DataUsage69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Internal inside project / collaboration"));
}),
_Cn/* ch3DataUsage68 */ = new T1(1,_Cm/* FormStructure.Chapter3.ch3DataUsage69 */),
_Co/* ch3DataUsage64 */ = {_:0,a:_Cn/* FormStructure.Chapter3.ch3DataUsage68 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Cl/* FormStructure.Chapter3.ch3DataUsage67 */,d:_Ck/* FormStructure.Chapter3.ch3DataUsage65 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_BV/* FormStructure.Chapter3.ch3DataUsage34 */},
_Cp/* ch3DataUsage63 */ = new T2(3,_Co/* FormStructure.Chapter3.ch3DataUsage64 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_Cq/* ch3DataUsage16 */ = new T2(1,_Cp/* FormStructure.Chapter3.ch3DataUsage63 */,_Ci/* FormStructure.Chapter3.ch3DataUsage17 */),
_Cr/* ch3DataUsage73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accesibility modes of your data:"));
}),
_Cs/* ch3DataUsage72 */ = new T1(1,_Cr/* FormStructure.Chapter3.ch3DataUsage73 */),
_Ct/* ch3DataUsage71 */ = {_:0,a:_Cs/* FormStructure.Chapter3.ch3DataUsage72 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Cu/* ch3DataUsage15 */ = new T3(8,_Ct/* FormStructure.Chapter3.ch3DataUsage71 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Cq/* FormStructure.Chapter3.ch3DataUsage16 */),
_Cv/* ch3DataUsage13 */ = new T2(1,_Cu/* FormStructure.Chapter3.ch3DataUsage15 */,_BE/* FormStructure.Chapter3.ch3DataUsage14 */),
_Cw/* ch3DataUsage104 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data represent a valuable asset that should be persisted as long as possible. How is your situation?"));
}),
_Cx/* ch3DataUsage103 */ = new T1(1,_Cw/* FormStructure.Chapter3.ch3DataUsage104 */),
_Cy/* ch3DataUsage106 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Maintenance and data sustainability"));
}),
_Cz/* ch3DataUsage105 */ = new T1(1,_Cy/* FormStructure.Chapter3.ch3DataUsage106 */),
_CA/* ch3DataUsage102 */ = {_:0,a:_Cz/* FormStructure.Chapter3.ch3DataUsage105 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Cx/* FormStructure.Chapter3.ch3DataUsage103 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_CB/* ch3DataUsage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("not limited"));
}),
_CC/* ch3DataUsage82 */ = new T1(0,_CB/* FormStructure.Chapter3.ch3DataUsage83 */),
_CD/* ch3DataUsage81 */ = new T2(1,_CC/* FormStructure.Chapter3.ch3DataUsage82 */,_I/* GHC.Types.[] */),
_CE/* ch3DataUsage85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_CF/* ch3DataUsage84 */ = new T1(0,_CE/* FormStructure.Chapter3.ch3DataUsage85 */),
_CG/* ch3DataUsage80 */ = new T2(1,_CF/* FormStructure.Chapter3.ch3DataUsage84 */,_CD/* FormStructure.Chapter3.ch3DataUsage81 */),
_CH/* ch3DataUsage87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("months"));
}),
_CI/* ch3DataUsage86 */ = new T1(0,_CH/* FormStructure.Chapter3.ch3DataUsage87 */),
_CJ/* ch3DataUsage79 */ = new T2(1,_CI/* FormStructure.Chapter3.ch3DataUsage86 */,_CG/* FormStructure.Chapter3.ch3DataUsage80 */),
_CK/* ch3DataUsage89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("weeks"));
}),
_CL/* ch3DataUsage88 */ = new T1(0,_CK/* FormStructure.Chapter3.ch3DataUsage89 */),
_CM/* ch3DataUsage78 */ = new T2(1,_CL/* FormStructure.Chapter3.ch3DataUsage88 */,_CJ/* FormStructure.Chapter3.ch3DataUsage79 */),
_CN/* ch3DataUsage92 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest considered period"));
}),
_CO/* ch3DataUsage91 */ = new T1(1,_CN/* FormStructure.Chapter3.ch3DataUsage92 */),
_CP/* ch3DataUsage94 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long are the data stored?"));
}),
_CQ/* ch3DataUsage93 */ = new T1(1,_CP/* FormStructure.Chapter3.ch3DataUsage94 */),
_CR/* ch3DataUsage90 */ = {_:0,a:_CQ/* FormStructure.Chapter3.ch3DataUsage93 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_CO/* FormStructure.Chapter3.ch3DataUsage91 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_CS/* ch3DataUsage77 */ = new T2(5,_CR/* FormStructure.Chapter3.ch3DataUsage90 */,_CM/* FormStructure.Chapter3.ch3DataUsage78 */),
_CT/* ch3DataUsage76 */ = new T2(1,_CS/* FormStructure.Chapter3.ch3DataUsage77 */,_I/* GHC.Types.[] */),
_CU/* ch3DataUsage98 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_CV/* ch3DataUsage97 */ = new T1(0,_CU/* FormStructure.Chapter3.ch3DataUsage98 */),
_CW/* ch3DataUsage96 */ = new T2(1,_CV/* FormStructure.Chapter3.ch3DataUsage97 */,_Ak/* FormStructure.Chapter3.ch3DataUsage4 */),
_CX/* ch3DataUsage101 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is the data sustainability plan defined?"));
}),
_CY/* ch3DataUsage100 */ = new T1(1,_CX/* FormStructure.Chapter3.ch3DataUsage101 */),
_CZ/* ch3DataUsage99 */ = {_:0,a:_CY/* FormStructure.Chapter3.ch3DataUsage100 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_D0/* ch3DataUsage95 */ = new T2(5,_CZ/* FormStructure.Chapter3.ch3DataUsage99 */,_CW/* FormStructure.Chapter3.ch3DataUsage96 */),
_D1/* ch3DataUsage75 */ = new T2(1,_D0/* FormStructure.Chapter3.ch3DataUsage95 */,_CT/* FormStructure.Chapter3.ch3DataUsage76 */),
_D2/* ch3DataUsage74 */ = new T3(8,_CA/* FormStructure.Chapter3.ch3DataUsage102 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_D1/* FormStructure.Chapter3.ch3DataUsage75 */),
_D3/* ch3DataUsage12 */ = new T2(1,_D2/* FormStructure.Chapter3.ch3DataUsage74 */,_Cv/* FormStructure.Chapter3.ch3DataUsage13 */),
_D4/* ch3DataUsage11 */ = new T2(1,_BD/* FormStructure.Chapter3.ch3DataUsage107 */,_D3/* FormStructure.Chapter3.ch3DataUsage12 */),
_D5/* ch3DataUsage174 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_D6/* ch3DataUsage173 */ = new T2(1,_D5/* FormStructure.Chapter3.ch3DataUsage174 */,_I/* GHC.Types.[] */),
_D7/* ch3DataUsage175 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_D8/* ch3DataUsage172 */ = new T2(1,_D7/* FormStructure.Chapter3.ch3DataUsage175 */,_D6/* FormStructure.Chapter3.ch3DataUsage173 */),
_D9/* ch3DataUsage176 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_Da/* ch3DataUsage171 */ = new T2(1,_D9/* FormStructure.Chapter3.ch3DataUsage176 */,_D8/* FormStructure.Chapter3.ch3DataUsage172 */),
_Db/* ch3DataUsage177 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_Dc/* ch3DataUsage170 */ = new T2(1,_Db/* FormStructure.Chapter3.ch3DataUsage177 */,_Da/* FormStructure.Chapter3.ch3DataUsage171 */),
_Dd/* ch3DataUsage169 */ = new T1(1,_Dc/* FormStructure.Chapter3.ch3DataUsage170 */),
_De/* ch3DataUsage179 */ = new T2(1,_sq/* FormStructure.Common.totalSum */,_I/* GHC.Types.[] */),
_Df/* ch3DataUsage181 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data from this stage"));
}),
_Dg/* ch3DataUsage180 */ = new T1(1,_Df/* FormStructure.Chapter3.ch3DataUsage181 */),
_Dh/* ch3DataUsage183 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_Di/* ch3DataUsage182 */ = new T2(1,_Dh/* FormStructure.Chapter3.ch3DataUsage183 */,_I/* GHC.Types.[] */),
_Dj/* ch3DataUsage185 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-volume"));
}),
_Dk/* ch3DataUsage184 */ = new T1(1,_Dj/* FormStructure.Chapter3.ch3DataUsage185 */),
_Dl/* ch3DataUsage187 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Resulting data volume"));
}),
_Dm/* ch3DataUsage186 */ = new T1(1,_Dl/* FormStructure.Chapter3.ch3DataUsage187 */),
_Dn/* ch3DataUsage178 */ = {_:0,a:_Dm/* FormStructure.Chapter3.ch3DataUsage186 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Dk/* FormStructure.Chapter3.ch3DataUsage184 */,d:_Di/* FormStructure.Chapter3.ch3DataUsage182 */,e:_Dg/* FormStructure.Chapter3.ch3DataUsage180 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_De/* FormStructure.Chapter3.ch3DataUsage179 */},
_Do/* ch3DataUsage168 */ = new T2(3,_Dn/* FormStructure.Chapter3.ch3DataUsage178 */,_Dd/* FormStructure.Chapter3.ch3DataUsage169 */),
_Dp/* ch3DataUsage167 */ = new T2(1,_Do/* FormStructure.Chapter3.ch3DataUsage168 */,_I/* GHC.Types.[] */),
_Dq/* ch3DataUsage190 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Output data volumes (for 2015)"));
}),
_Dr/* ch3DataUsage189 */ = new T1(1,_Dq/* FormStructure.Chapter3.ch3DataUsage190 */),
_Ds/* ch3DataUsage188 */ = {_:0,a:_Dr/* FormStructure.Chapter3.ch3DataUsage189 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Dt/* ch3DataUsage166 */ = new T3(8,_Ds/* FormStructure.Chapter3.ch3DataUsage188 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Dp/* FormStructure.Chapter3.ch3DataUsage167 */),
_Du/* ch3DataUsage10 */ = new T2(1,_Dt/* FormStructure.Chapter3.ch3DataUsage166 */,_D4/* FormStructure.Chapter3.ch3DataUsage11 */),
_Dv/* ch3DataUsage207 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-sum"));
}),
_Dw/* ch3DataUsage206 */ = new T1(1,_Dv/* FormStructure.Chapter3.ch3DataUsage207 */),
_Dx/* ch3DataUsage205 */ = {_:0,a:_AD/* FormStructure.Chapter3.ch3DataUsage30 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Dw/* FormStructure.Chapter3.ch3DataUsage206 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_AB/* FormStructure.Chapter3.ch3DataUsage24 */},
_Dy/* ch3DataUsage204 */ = new T2(3,_Dx/* FormStructure.Chapter3.ch3DataUsage205 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_Dz/* ch3DataUsage203 */ = new T2(1,_Dy/* FormStructure.Chapter3.ch3DataUsage204 */,_I/* GHC.Types.[] */),
_DA/* ch3DataUsage215 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-worldwide"));
}),
_DB/* ch3DataUsage214 */ = new T2(1,_DA/* FormStructure.Chapter3.ch3DataUsage215 */,_I/* GHC.Types.[] */),
_DC/* ch3DataUsage216 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-european"));
}),
_DD/* ch3DataUsage213 */ = new T2(1,_DC/* FormStructure.Chapter3.ch3DataUsage216 */,_DB/* FormStructure.Chapter3.ch3DataUsage214 */),
_DE/* ch3DataUsage217 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-national"));
}),
_DF/* ch3DataUsage212 */ = new T2(1,_DE/* FormStructure.Chapter3.ch3DataUsage217 */,_DD/* FormStructure.Chapter3.ch3DataUsage213 */),
_DG/* ch3DataUsage218 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-external-internal-funding-institutional"));
}),
_DH/* ch3DataUsage211 */ = new T2(1,_DG/* FormStructure.Chapter3.ch3DataUsage218 */,_DF/* FormStructure.Chapter3.ch3DataUsage212 */),
_DI/* ch3DataUsage_fundingSumRule1 */ = new T2(0,_DH/* FormStructure.Chapter3.ch3DataUsage211 */,_Dv/* FormStructure.Chapter3.ch3DataUsage207 */),
_DJ/* ch3DataUsage210 */ = new T2(1,_DI/* FormStructure.Chapter3.ch3DataUsage_fundingSumRule1 */,_AN/* FormStructure.Chapter3.ch3DataUsage123 */),
_DK/* ch3DataUsage219 */ = new T1(1,_DA/* FormStructure.Chapter3.ch3DataUsage215 */),
_DL/* ch3DataUsage209 */ = {_:0,a:_B0/* FormStructure.Chapter3.ch3DataUsage135 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_DK/* FormStructure.Chapter3.ch3DataUsage219 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_DJ/* FormStructure.Chapter3.ch3DataUsage210 */},
_DM/* ch3DataUsage208 */ = new T2(3,_DL/* FormStructure.Chapter3.ch3DataUsage209 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_DN/* ch3DataUsage202 */ = new T2(1,_DM/* FormStructure.Chapter3.ch3DataUsage208 */,_Dz/* FormStructure.Chapter3.ch3DataUsage203 */),
_DO/* ch3DataUsage222 */ = new T1(1,_DC/* FormStructure.Chapter3.ch3DataUsage216 */),
_DP/* ch3DataUsage221 */ = {_:0,a:_B6/* FormStructure.Chapter3.ch3DataUsage140 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_DO/* FormStructure.Chapter3.ch3DataUsage222 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_DJ/* FormStructure.Chapter3.ch3DataUsage210 */},
_DQ/* ch3DataUsage220 */ = new T2(3,_DP/* FormStructure.Chapter3.ch3DataUsage221 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_DR/* ch3DataUsage201 */ = new T2(1,_DQ/* FormStructure.Chapter3.ch3DataUsage220 */,_DN/* FormStructure.Chapter3.ch3DataUsage202 */),
_DS/* ch3DataUsage225 */ = new T1(1,_DE/* FormStructure.Chapter3.ch3DataUsage217 */),
_DT/* ch3DataUsage224 */ = {_:0,a:_Bc/* FormStructure.Chapter3.ch3DataUsage145 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_DS/* FormStructure.Chapter3.ch3DataUsage225 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_DJ/* FormStructure.Chapter3.ch3DataUsage210 */},
_DU/* ch3DataUsage223 */ = new T2(3,_DT/* FormStructure.Chapter3.ch3DataUsage224 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_DV/* ch3DataUsage200 */ = new T2(1,_DU/* FormStructure.Chapter3.ch3DataUsage223 */,_DR/* FormStructure.Chapter3.ch3DataUsage201 */),
_DW/* ch3DataUsage228 */ = new T1(1,_DG/* FormStructure.Chapter3.ch3DataUsage218 */),
_DX/* ch3DataUsage227 */ = {_:0,a:_Bi/* FormStructure.Chapter3.ch3DataUsage150 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_DW/* FormStructure.Chapter3.ch3DataUsage228 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_DJ/* FormStructure.Chapter3.ch3DataUsage210 */},
_DY/* ch3DataUsage226 */ = new T2(3,_DX/* FormStructure.Chapter3.ch3DataUsage227 */,_AG/* FormStructure.Chapter3.ch3DataUsage21 */),
_DZ/* ch3DataUsage199 */ = new T2(1,_DY/* FormStructure.Chapter3.ch3DataUsage226 */,_DV/* FormStructure.Chapter3.ch3DataUsage200 */),
_E0/* ch3DataUsage198 */ = new T3(8,_Bo/* FormStructure.Chapter3.ch3DataUsage152 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_DZ/* FormStructure.Chapter3.ch3DataUsage199 */),
_E1/* ch3DataUsage197 */ = new T2(1,_E0/* FormStructure.Chapter3.ch3DataUsage198 */,_I/* GHC.Types.[] */),
_E2/* ch3DataUsage196 */ = new T2(1,_Bw/* FormStructure.Chapter3.ch3DataUsage155 */,_E1/* FormStructure.Chapter3.ch3DataUsage197 */),
_E3/* ch3DataUsage231 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Cost of external data purchases"));
}),
_E4/* ch3DataUsage230 */ = new T1(1,_E3/* FormStructure.Chapter3.ch3DataUsage231 */),
_E5/* ch3DataUsage229 */ = {_:0,a:_E4/* FormStructure.Chapter3.ch3DataUsage230 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_E6/* ch3DataUsage195 */ = new T3(8,_E5/* FormStructure.Chapter3.ch3DataUsage229 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_E2/* FormStructure.Chapter3.ch3DataUsage196 */),
_E7/* ch3DataUsage194 */ = new T2(1,_E6/* FormStructure.Chapter3.ch3DataUsage195 */,_I/* GHC.Types.[] */),
_E8/* ch3DataUsage235 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External data that are not publicly available and are produced specifically for your needs."));
}),
_E9/* ch3DataUsage234 */ = new T1(1,_E8/* FormStructure.Chapter3.ch3DataUsage235 */),
_Ea/* ch3DataUsage237 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_L_3"));
}),
_Eb/* ch3DataUsage236 */ = new T2(1,_Ea/* FormStructure.Chapter3.ch3DataUsage237 */,_I/* GHC.Types.[] */),
_Ec/* ch3DataUsage239 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Incoming external specific raw data volume"));
}),
_Ed/* ch3DataUsage238 */ = new T1(1,_Ec/* FormStructure.Chapter3.ch3DataUsage239 */),
_Ee/* ch3DataUsage233 */ = {_:0,a:_Ed/* FormStructure.Chapter3.ch3DataUsage238 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Eb/* FormStructure.Chapter3.ch3DataUsage236 */,e:_E9/* FormStructure.Chapter3.ch3DataUsage234 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ef/* ch3DataUsage232 */ = new T2(3,_Ee/* FormStructure.Chapter3.ch3DataUsage233 */,_Dd/* FormStructure.Chapter3.ch3DataUsage169 */),
_Eg/* ch3DataUsage193 */ = new T2(1,_Ef/* FormStructure.Chapter3.ch3DataUsage232 */,_E7/* FormStructure.Chapter3.ch3DataUsage194 */),
_Eh/* ch3DataUsage241 */ = new T1(0,_D7/* FormStructure.Chapter3.ch3DataUsage175 */),
_Ei/* ch3DataUsage243 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_Ej/* ch3DataUsage245 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_Ek/* ch3DataUsage244 */ = new T2(1,_Ej/* FormStructure.Chapter3.ch3DataUsage245 */,_I/* GHC.Types.[] */),
_El/* ch3DataUsage247 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("sec-input-volume"));
}),
_Em/* ch3DataUsage246 */ = new T1(1,_El/* FormStructure.Chapter3.ch3DataUsage247 */),
_En/* ch3DataUsage249 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Inhouse produced data volume"));
}),
_Eo/* ch3DataUsage248 */ = new T1(1,_En/* FormStructure.Chapter3.ch3DataUsage249 */),
_Ep/* ch3DataUsage242 */ = {_:0,a:_Eo/* FormStructure.Chapter3.ch3DataUsage248 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Em/* FormStructure.Chapter3.ch3DataUsage246 */,d:_Ek/* FormStructure.Chapter3.ch3DataUsage244 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_Ei/* FormStructure.Chapter3.ch3DataUsage243 */},
_Eq/* ch3DataUsage240 */ = new T2(3,_Ep/* FormStructure.Chapter3.ch3DataUsage242 */,_Eh/* FormStructure.Chapter3.ch3DataUsage241 */),
_Er/* ch3DataUsage192 */ = new T2(1,_Eq/* FormStructure.Chapter3.ch3DataUsage240 */,_Eg/* FormStructure.Chapter3.ch3DataUsage193 */),
_Es/* ch3DataUsage252 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Input data (for 2015)"));
}),
_Et/* ch3DataUsage251 */ = new T1(1,_Es/* FormStructure.Chapter3.ch3DataUsage252 */),
_Eu/* ch3DataUsage250 */ = {_:0,a:_Et/* FormStructure.Chapter3.ch3DataUsage251 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Ev/* ch3DataUsage191 */ = new T3(8,_Eu/* FormStructure.Chapter3.ch3DataUsage250 */,_At/* FormStructure.Chapter3.ch3DataUsage70 */,_Er/* FormStructure.Chapter3.ch3DataUsage192 */),
_Ew/* ch3DataUsage9 */ = new T2(1,_Ev/* FormStructure.Chapter3.ch3DataUsage191 */,_Du/* FormStructure.Chapter3.ch3DataUsage10 */),
_Ex/* ch3DataUsage8 */ = new T2(1,_Au/* FormStructure.Chapter3.ch3DataUsage253 */,_Ew/* FormStructure.Chapter3.ch3DataUsage9 */),
_Ey/* ch3DataUsage7 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_CU/* FormStructure.Chapter3.ch3DataUsage98 */,_Ex/* FormStructure.Chapter3.ch3DataUsage8 */),
_Ez/* ch3DataUsage3 */ = new T2(1,_Ey/* FormStructure.Chapter3.ch3DataUsage7 */,_Ak/* FormStructure.Chapter3.ch3DataUsage4 */),
_EA/* ch3DataUsage2 */ = new T2(5,_Ah/* FormStructure.Chapter3.ch3DataUsage262 */,_Ez/* FormStructure.Chapter3.ch3DataUsage3 */),
_EB/* ch3DataUsage1 */ = new T2(1,_EA/* FormStructure.Chapter3.ch3DataUsage2 */,_I/* GHC.Types.[] */),
_EC/* ch3DataUsage267 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("3.Usage "));
}),
_ED/* ch3DataUsage266 */ = new T1(1,_EC/* FormStructure.Chapter3.ch3DataUsage267 */),
_EE/* ch3DataUsage265 */ = {_:0,a:_ED/* FormStructure.Chapter3.ch3DataUsage266 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_EF/* ch3DataUsage */ = new T2(7,_EE/* FormStructure.Chapter3.ch3DataUsage265 */,_EB/* FormStructure.Chapter3.ch3DataUsage1 */),
_EG/* ch4DataStorage3 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_EH/* ch4DataStorage46 */ = 0,
_EI/* ch4DataStorage49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Storage providers"));
}),
_EJ/* ch4DataStorage48 */ = new T1(1,_EI/* FormStructure.Chapter4.ch4DataStorage49 */),
_EK/* ch4DataStorage47 */ = {_:0,a:_EJ/* FormStructure.Chapter4.ch4DataStorage48 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_EL/* ch4DataStorage11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("%"));
}),
_EM/* ch4DataStorage10 */ = new T1(0,_EL/* FormStructure.Chapter4.ch4DataStorage11 */),
_EN/* ch4DataStorage26 */ = function(_EO/* sd9A */){
  var _EP/* sd9B */ = E(_EO/* sd9A */);
  return (_EP/* sd9B */<0) ? false : _EP/* sd9B */<=100;
},
_EQ/* ch4DataStorage25 */ = new T1(4,_EN/* FormStructure.Chapter4.ch4DataStorage26 */),
_ER/* ch4DataStorage24 */ = new T2(1,_EQ/* FormStructure.Chapter4.ch4DataStorage25 */,_I/* GHC.Types.[] */),
_ES/* ch4DataStorage18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-providers-sum"));
}),
_ET/* ch4DataStorage30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-external"));
}),
_EU/* ch4DataStorage29 */ = new T2(1,_ET/* FormStructure.Chapter4.ch4DataStorage30 */,_I/* GHC.Types.[] */),
_EV/* ch4DataStorage31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-institutional"));
}),
_EW/* ch4DataStorage28 */ = new T2(1,_EV/* FormStructure.Chapter4.ch4DataStorage31 */,_EU/* FormStructure.Chapter4.ch4DataStorage29 */),
_EX/* ch4DataStorage32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("storage-provider-group"));
}),
_EY/* ch4DataStorage27 */ = new T2(1,_EX/* FormStructure.Chapter4.ch4DataStorage32 */,_EW/* FormStructure.Chapter4.ch4DataStorage28 */),
_EZ/* ch4DataStorage_storageSumRule */ = new T2(0,_EY/* FormStructure.Chapter4.ch4DataStorage27 */,_ES/* FormStructure.Chapter4.ch4DataStorage18 */),
_F0/* ch4DataStorage23 */ = new T2(1,_EZ/* FormStructure.Chapter4.ch4DataStorage_storageSumRule */,_ER/* FormStructure.Chapter4.ch4DataStorage24 */),
_F1/* ch4DataStorage43 */ = new T1(1,_EX/* FormStructure.Chapter4.ch4DataStorage32 */),
_F2/* ch4DataStorage45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Group\'s local"));
}),
_F3/* ch4DataStorage44 */ = new T1(1,_F2/* FormStructure.Chapter4.ch4DataStorage45 */),
_F4/* ch4DataStorage42 */ = {_:0,a:_F3/* FormStructure.Chapter4.ch4DataStorage44 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_F1/* FormStructure.Chapter4.ch4DataStorage43 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_F0/* FormStructure.Chapter4.ch4DataStorage23 */},
_F5/* ch4DataStorage41 */ = new T2(3,_F4/* FormStructure.Chapter4.ch4DataStorage42 */,_EM/* FormStructure.Chapter4.ch4DataStorage10 */),
_F6/* ch4DataStorage38 */ = new T1(1,_EV/* FormStructure.Chapter4.ch4DataStorage31 */),
_F7/* ch4DataStorage40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Institutional"));
}),
_F8/* ch4DataStorage39 */ = new T1(1,_F7/* FormStructure.Chapter4.ch4DataStorage40 */),
_F9/* ch4DataStorage37 */ = {_:0,a:_F8/* FormStructure.Chapter4.ch4DataStorage39 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_F6/* FormStructure.Chapter4.ch4DataStorage38 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_F0/* FormStructure.Chapter4.ch4DataStorage23 */},
_Fa/* ch4DataStorage36 */ = new T2(3,_F9/* FormStructure.Chapter4.ch4DataStorage37 */,_EM/* FormStructure.Chapter4.ch4DataStorage10 */),
_Fb/* ch4DataStorage33 */ = new T1(1,_ET/* FormStructure.Chapter4.ch4DataStorage30 */),
_Fc/* ch4DataStorage35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("External Provider"));
}),
_Fd/* ch4DataStorage34 */ = new T1(1,_Fc/* FormStructure.Chapter4.ch4DataStorage35 */),
_Fe/* ch4DataStorage22 */ = {_:0,a:_Fd/* FormStructure.Chapter4.ch4DataStorage34 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Fb/* FormStructure.Chapter4.ch4DataStorage33 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_F0/* FormStructure.Chapter4.ch4DataStorage23 */},
_Ff/* ch4DataStorage21 */ = new T2(3,_Fe/* FormStructure.Chapter4.ch4DataStorage22 */,_EM/* FormStructure.Chapter4.ch4DataStorage10 */),
_Fg/* ch4DataStorage16 */ = function(_Fh/* sd9G */){
  return (E(_Fh/* sd9G */)==100) ? true : false;
},
_Fi/* ch4DataStorage15 */ = new T1(4,_Fg/* FormStructure.Chapter4.ch4DataStorage16 */),
_Fj/* ch4DataStorage14 */ = new T2(1,_Fi/* FormStructure.Chapter4.ch4DataStorage15 */,_I/* GHC.Types.[] */),
_Fk/* ch4DataStorage13 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_Fj/* FormStructure.Chapter4.ch4DataStorage14 */),
_Fl/* ch4DataStorage17 */ = new T1(1,_ES/* FormStructure.Chapter4.ch4DataStorage18 */),
_Fm/* ch4DataStorage20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sum"));
}),
_Fn/* ch4DataStorage19 */ = new T1(1,_Fm/* FormStructure.Chapter4.ch4DataStorage20 */),
_Fo/* ch4DataStorage12 */ = {_:0,a:_Fn/* FormStructure.Chapter4.ch4DataStorage19 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_Fl/* FormStructure.Chapter4.ch4DataStorage17 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_Fk/* FormStructure.Chapter4.ch4DataStorage13 */},
_Fp/* ch4DataStorage9 */ = new T2(3,_Fo/* FormStructure.Chapter4.ch4DataStorage12 */,_EM/* FormStructure.Chapter4.ch4DataStorage10 */),
_Fq/* ch4DataStorage8 */ = new T2(1,_Fp/* FormStructure.Chapter4.ch4DataStorage9 */,_I/* GHC.Types.[] */),
_Fr/* ch4DataStorage7 */ = new T2(1,_Ff/* FormStructure.Chapter4.ch4DataStorage21 */,_Fq/* FormStructure.Chapter4.ch4DataStorage8 */),
_Fs/* ch4DataStorage6 */ = new T2(1,_Fa/* FormStructure.Chapter4.ch4DataStorage36 */,_Fr/* FormStructure.Chapter4.ch4DataStorage7 */),
_Ft/* ch4DataStorage5 */ = new T2(1,_F5/* FormStructure.Chapter4.ch4DataStorage41 */,_Fs/* FormStructure.Chapter4.ch4DataStorage6 */),
_Fu/* ch4DataStorage4 */ = new T3(8,_EK/* FormStructure.Chapter4.ch4DataStorage47 */,_EH/* FormStructure.Chapter4.ch4DataStorage46 */,_Ft/* FormStructure.Chapter4.ch4DataStorage5 */),
_Fv/* ch4DataStorage2 */ = new T2(1,_Fu/* FormStructure.Chapter4.ch4DataStorage4 */,_EG/* FormStructure.Chapter4.ch4DataStorage3 */),
_Fw/* ch4DataStorage60 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_Fx/* ch4DataStorage59 */ = new T2(1,_Fw/* FormStructure.Chapter4.ch4DataStorage60 */,_I/* GHC.Types.[] */),
_Fy/* ch4DataStorage61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_Fz/* ch4DataStorage58 */ = new T2(1,_Fy/* FormStructure.Chapter4.ch4DataStorage61 */,_Fx/* FormStructure.Chapter4.ch4DataStorage59 */),
_FA/* ch4DataStorage62 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_FB/* ch4DataStorage57 */ = new T2(1,_FA/* FormStructure.Chapter4.ch4DataStorage62 */,_Fz/* FormStructure.Chapter4.ch4DataStorage58 */),
_FC/* ch4DataStorage63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_FD/* ch4DataStorage56 */ = new T2(1,_FC/* FormStructure.Chapter4.ch4DataStorage63 */,_FB/* FormStructure.Chapter4.ch4DataStorage57 */),
_FE/* ch4DataStorage55 */ = new T1(1,_FD/* FormStructure.Chapter4.ch4DataStorage56 */),
_FF/* ch4DataStorage66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of backups"));
}),
_FG/* ch4DataStorage65 */ = new T1(1,_FF/* FormStructure.Chapter4.ch4DataStorage66 */),
_FH/* ch4DataStorage64 */ = {_:0,a:_FG/* FormStructure.Chapter4.ch4DataStorage65 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_FI/* ch4DataStorage54 */ = new T2(3,_FH/* FormStructure.Chapter4.ch4DataStorage64 */,_FE/* FormStructure.Chapter4.ch4DataStorage55 */),
_FJ/* ch4DataStorage53 */ = new T2(1,_FI/* FormStructure.Chapter4.ch4DataStorage54 */,_I/* GHC.Types.[] */),
_FK/* ch4DataStorage70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume of data stored at the end of 2015"));
}),
_FL/* ch4DataStorage69 */ = new T1(1,_FK/* FormStructure.Chapter4.ch4DataStorage70 */),
_FM/* ch4DataStorage68 */ = {_:0,a:_FL/* FormStructure.Chapter4.ch4DataStorage69 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_FN/* ch4DataStorage67 */ = new T2(3,_FM/* FormStructure.Chapter4.ch4DataStorage68 */,_FE/* FormStructure.Chapter4.ch4DataStorage55 */),
_FO/* ch4DataStorage52 */ = new T2(1,_FN/* FormStructure.Chapter4.ch4DataStorage67 */,_FJ/* FormStructure.Chapter4.ch4DataStorage53 */),
_FP/* ch4DataStorage72 */ = new T1(0,_Fy/* FormStructure.Chapter4.ch4DataStorage61 */),
_FQ/* ch4DataStorage74 */ = new T2(1,_s4/* FormEngine.FormItem.ReadOnlyRule */,_I/* GHC.Types.[] */),
_FR/* ch4DataStorage76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("total-volume"));
}),
_FS/* ch4DataStorage75 */ = new T1(1,_FR/* FormStructure.Chapter4.ch4DataStorage76 */),
_FT/* ch4DataStorage78 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total volume produced in 2015"));
}),
_FU/* ch4DataStorage77 */ = new T1(1,_FT/* FormStructure.Chapter4.ch4DataStorage78 */),
_FV/* ch4DataStorage73 */ = {_:0,a:_FU/* FormStructure.Chapter4.ch4DataStorage77 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_FS/* FormStructure.Chapter4.ch4DataStorage75 */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_FQ/* FormStructure.Chapter4.ch4DataStorage74 */},
_FW/* ch4DataStorage71 */ = new T2(3,_FV/* FormStructure.Chapter4.ch4DataStorage73 */,_FP/* FormStructure.Chapter4.ch4DataStorage72 */),
_FX/* ch4DataStorage51 */ = new T2(1,_FW/* FormStructure.Chapter4.ch4DataStorage71 */,_FO/* FormStructure.Chapter4.ch4DataStorage52 */),
_FY/* ch4DataStorage81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Just scientic data volumes (without backups and scratch/tmp) are in question."));
}),
_FZ/* ch4DataStorage80 */ = new T1(1,_FY/* FormStructure.Chapter4.ch4DataStorage81 */),
_G0/* ch4DataStorage83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data volumes"));
}),
_G1/* ch4DataStorage82 */ = new T1(1,_G0/* FormStructure.Chapter4.ch4DataStorage83 */),
_G2/* ch4DataStorage79 */ = {_:0,a:_G1/* FormStructure.Chapter4.ch4DataStorage82 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_FZ/* FormStructure.Chapter4.ch4DataStorage80 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_G3/* ch4DataStorage50 */ = new T3(8,_G2/* FormStructure.Chapter4.ch4DataStorage79 */,_EH/* FormStructure.Chapter4.ch4DataStorage46 */,_FX/* FormStructure.Chapter4.ch4DataStorage51 */),
_G4/* ch4DataStorage1 */ = new T2(1,_G3/* FormStructure.Chapter4.ch4DataStorage50 */,_Fv/* FormStructure.Chapter4.ch4DataStorage2 */),
_G5/* ch4DataStorage86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("4.Storage "));
}),
_G6/* ch4DataStorage85 */ = new T1(1,_G5/* FormStructure.Chapter4.ch4DataStorage86 */),
_G7/* ch4DataStorage84 */ = {_:0,a:_G6/* FormStructure.Chapter4.ch4DataStorage85 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_G8/* ch4DataStorage */ = new T2(7,_G7/* FormStructure.Chapter4.ch4DataStorage84 */,_G4/* FormStructure.Chapter4.ch4DataStorage1 */),
_G9/* ch5DataAccessibility2 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_Ga/* ch5DataAccessibility32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you provide data accessibility for external parties?"));
}),
_Gb/* ch5DataAccessibility31 */ = new T1(1,_Ga/* FormStructure.Chapter5.ch5DataAccessibility32 */),
_Gc/* ch5DataAccessibility30 */ = {_:0,a:_Gb/* FormStructure.Chapter5.ch5DataAccessibility31 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Gd/* ch5DataAccessibility7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_Ge/* ch5DataAccessibility6 */ = new T1(0,_Gd/* FormStructure.Chapter5.ch5DataAccessibility7 */),
_Gf/* ch5DataAccessibility5 */ = new T2(1,_Ge/* FormStructure.Chapter5.ch5DataAccessibility6 */,_I/* GHC.Types.[] */),
_Gg/* ch5DataAccessibility29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_Gh/* ch5DataAccessibility16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("URLs to web pages / data source or other accessibility link"));
}),
_Gi/* ch5DataAccessibility15 */ = new T1(1,_Gh/* FormStructure.Chapter5.ch5DataAccessibility16 */),
_Gj/* ch5DataAccessibility18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Links to your services"));
}),
_Gk/* ch5DataAccessibility17 */ = new T1(1,_Gj/* FormStructure.Chapter5.ch5DataAccessibility18 */),
_Gl/* ch5DataAccessibility14 */ = {_:0,a:_Gk/* FormStructure.Chapter5.ch5DataAccessibility17 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Gi/* FormStructure.Chapter5.ch5DataAccessibility15 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Gm/* ch5DataAccessibility13 */ = new T1(1,_Gl/* FormStructure.Chapter5.ch5DataAccessibility14 */),
_Gn/* ch5DataAccessibility12 */ = new T2(1,_Gm/* FormStructure.Chapter5.ch5DataAccessibility13 */,_I/* GHC.Types.[] */),
_Go/* ch5DataAccessibility22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For inspiration, click the red box in the figure"));
}),
_Gp/* ch5DataAccessibility21 */ = new T1(1,_Go/* FormStructure.Chapter5.ch5DataAccessibility22 */),
_Gq/* ch5DataAccessibility24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How do you make your data accessible?"));
}),
_Gr/* ch5DataAccessibility23 */ = new T1(1,_Gq/* FormStructure.Chapter5.ch5DataAccessibility24 */),
_Gs/* ch5DataAccessibility20 */ = {_:0,a:_Gr/* FormStructure.Chapter5.ch5DataAccessibility23 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Gp/* FormStructure.Chapter5.ch5DataAccessibility21 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Gt/* ch5DataAccessibility19 */ = new T1(1,_Gs/* FormStructure.Chapter5.ch5DataAccessibility20 */),
_Gu/* ch5DataAccessibility11 */ = new T2(1,_Gt/* FormStructure.Chapter5.ch5DataAccessibility19 */,_Gn/* FormStructure.Chapter5.ch5DataAccessibility12 */),
_Gv/* ch5DataAccessibility25 */ = 1,
_Gw/* ch5DataAccessibility28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Accessibility details"));
}),
_Gx/* ch5DataAccessibility27 */ = new T1(1,_Gw/* FormStructure.Chapter5.ch5DataAccessibility28 */),
_Gy/* ch5DataAccessibility26 */ = {_:0,a:_Gx/* FormStructure.Chapter5.ch5DataAccessibility27 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Gz/* ch5DataAccessibility10 */ = new T3(8,_Gy/* FormStructure.Chapter5.ch5DataAccessibility26 */,_Gv/* FormStructure.Chapter5.ch5DataAccessibility25 */,_Gu/* FormStructure.Chapter5.ch5DataAccessibility11 */),
_GA/* ch5DataAccessibility9 */ = new T2(1,_Gz/* FormStructure.Chapter5.ch5DataAccessibility10 */,_I/* GHC.Types.[] */),
_GB/* ch5DataAccessibility8 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_Gg/* FormStructure.Chapter5.ch5DataAccessibility29 */,_GA/* FormStructure.Chapter5.ch5DataAccessibility9 */),
_GC/* ch5DataAccessibility4 */ = new T2(1,_GB/* FormStructure.Chapter5.ch5DataAccessibility8 */,_Gf/* FormStructure.Chapter5.ch5DataAccessibility5 */),
_GD/* ch5DataAccessibility3 */ = new T2(5,_Gc/* FormStructure.Chapter5.ch5DataAccessibility30 */,_GC/* FormStructure.Chapter5.ch5DataAccessibility4 */),
_GE/* ch5DataAccessibility1 */ = new T2(1,_GD/* FormStructure.Chapter5.ch5DataAccessibility3 */,_G9/* FormStructure.Chapter5.ch5DataAccessibility2 */),
_GF/* ch5DataAccessibility35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("5.Accessibility "));
}),
_GG/* ch5DataAccessibility34 */ = new T1(1,_GF/* FormStructure.Chapter5.ch5DataAccessibility35 */),
_GH/* ch5DataAccessibility33 */ = {_:0,a:_GG/* FormStructure.Chapter5.ch5DataAccessibility34 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_GI/* ch5DataAccessibility */ = new T2(7,_GH/* FormStructure.Chapter5.ch5DataAccessibility33 */,_GE/* FormStructure.Chapter5.ch5DataAccessibility1 */),
_GJ/* ch6DataManagement13 */ = 0,
_GK/* ch6DataManagement28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("No"));
}),
_GL/* ch6DataManagement27 */ = new T1(0,_GK/* FormStructure.Chapter6.ch6DataManagement28 */),
_GM/* ch6DataManagement26 */ = new T2(1,_GL/* FormStructure.Chapter6.ch6DataManagement27 */,_I/* GHC.Types.[] */),
_GN/* xhow3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How?"));
}),
_GO/* xhow2 */ = new T1(1,_GN/* FormStructure.Common.xhow3 */),
_GP/* xhow1 */ = {_:0,a:_GO/* FormStructure.Common.xhow2 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_GQ/* xhow */ = new T1(1,_GP/* FormStructure.Common.xhow1 */),
_GR/* ch6DataManagement30 */ = new T2(1,_GQ/* FormStructure.Common.xhow */,_I/* GHC.Types.[] */),
_GS/* ch6DataManagement31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Yes"));
}),
_GT/* ch6DataManagement29 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_GS/* FormStructure.Chapter6.ch6DataManagement31 */,_GR/* FormStructure.Chapter6.ch6DataManagement30 */),
_GU/* ch6DataManagement25 */ = new T2(1,_GT/* FormStructure.Chapter6.ch6DataManagement29 */,_GM/* FormStructure.Chapter6.ch6DataManagement26 */),
_GV/* ch6DataManagement34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you apply some form of data stewardship?"));
}),
_GW/* ch6DataManagement33 */ = new T1(1,_GV/* FormStructure.Chapter6.ch6DataManagement34 */),
_GX/* ch6DataManagement32 */ = {_:0,a:_GW/* FormStructure.Chapter6.ch6DataManagement33 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_GY/* ch6DataManagement24 */ = new T2(5,_GX/* FormStructure.Chapter6.ch6DataManagement32 */,_GU/* FormStructure.Chapter6.ch6DataManagement25 */),
_GZ/* ch6DataManagement23 */ = new T2(1,_GY/* FormStructure.Chapter6.ch6DataManagement24 */,_I/* GHC.Types.[] */),
_H0/* ch6DataManagement37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("years"));
}),
_H1/* ch6DataManagement36 */ = new T1(0,_H0/* FormStructure.Chapter6.ch6DataManagement37 */),
_H2/* ch6DataManagement40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Longest required sustainability"));
}),
_H3/* ch6DataManagement39 */ = new T1(1,_H2/* FormStructure.Chapter6.ch6DataManagement40 */),
_H4/* ch6DataManagement38 */ = {_:0,a:_H3/* FormStructure.Chapter6.ch6DataManagement39 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_H5/* ch6DataManagement35 */ = new T2(3,_H4/* FormStructure.Chapter6.ch6DataManagement38 */,_H1/* FormStructure.Chapter6.ch6DataManagement36 */),
_H6/* ch6DataManagement22 */ = new T2(1,_H5/* FormStructure.Chapter6.ch6DataManagement35 */,_GZ/* FormStructure.Chapter6.ch6DataManagement23 */),
_H7/* ch6DataManagement51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("How long"));
}),
_H8/* ch6DataManagement50 */ = new T1(1,_H7/* FormStructure.Chapter6.ch6DataManagement51 */),
_H9/* ch6DataManagement49 */ = {_:0,a:_H8/* FormStructure.Chapter6.ch6DataManagement50 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ha/* ch6DataManagement48 */ = new T2(3,_H9/* FormStructure.Chapter6.ch6DataManagement49 */,_H1/* FormStructure.Chapter6.ch6DataManagement36 */),
_Hb/* ch6DataManagement47 */ = new T2(1,_Ha/* FormStructure.Chapter6.ch6DataManagement48 */,_I/* GHC.Types.[] */),
_Hc/* ch6DataManagement52 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Hd/* ch6DataManagement46 */ = new T3(8,_Hc/* FormStructure.Chapter6.ch6DataManagement52 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_Hb/* FormStructure.Chapter6.ch6DataManagement47 */),
_He/* ch6DataManagement45 */ = new T2(1,_Hd/* FormStructure.Chapter6.ch6DataManagement46 */,_I/* GHC.Types.[] */),
_Hf/* ch6DataManagement53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("short-term"));
}),
_Hg/* ch6DataManagement44 */ = new T3(1,_av/* FormEngine.FormItem.NoNumbering */,_Hf/* FormStructure.Chapter6.ch6DataManagement53 */,_He/* FormStructure.Chapter6.ch6DataManagement45 */),
_Hh/* ch6DataManagement43 */ = new T2(1,_Hg/* FormStructure.Chapter6.ch6DataManagement44 */,_I/* GHC.Types.[] */),
_Hi/* ch6DataManagement55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("long-term, continuous funding"));
}),
_Hj/* ch6DataManagement54 */ = new T1(0,_Hi/* FormStructure.Chapter6.ch6DataManagement55 */),
_Hk/* ch6DataManagement42 */ = new T2(1,_Hj/* FormStructure.Chapter6.ch6DataManagement54 */,_Hh/* FormStructure.Chapter6.ch6DataManagement43 */),
_Hl/* ch6DataManagement58 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Sustainability"));
}),
_Hm/* ch6DataManagement57 */ = new T1(1,_Hl/* FormStructure.Chapter6.ch6DataManagement58 */),
_Hn/* ch6DataManagement56 */ = {_:0,a:_Hm/* FormStructure.Chapter6.ch6DataManagement57 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ho/* ch6DataManagement41 */ = new T2(5,_Hn/* FormStructure.Chapter6.ch6DataManagement56 */,_Hk/* FormStructure.Chapter6.ch6DataManagement42 */),
_Hp/* ch6DataManagement21 */ = new T2(1,_Ho/* FormStructure.Chapter6.ch6DataManagement41 */,_H6/* FormStructure.Chapter6.ch6DataManagement22 */),
_Hq/* ch6DataManagement63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("yes"));
}),
_Hr/* ch6DataManagement62 */ = new T1(0,_Hq/* FormStructure.Chapter6.ch6DataManagement63 */),
_Hs/* ch6DataManagement61 */ = new T2(1,_Hr/* FormStructure.Chapter6.ch6DataManagement62 */,_I/* GHC.Types.[] */),
_Ht/* ch6DataManagement65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("no"));
}),
_Hu/* ch6DataManagement64 */ = new T1(0,_Ht/* FormStructure.Chapter6.ch6DataManagement65 */),
_Hv/* ch6DataManagement60 */ = new T2(1,_Hu/* FormStructure.Chapter6.ch6DataManagement64 */,_Hs/* FormStructure.Chapter6.ch6DataManagement61 */),
_Hw/* ch6DataManagement68 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Is data actuality maintained (updates)?"));
}),
_Hx/* ch6DataManagement67 */ = new T1(1,_Hw/* FormStructure.Chapter6.ch6DataManagement68 */),
_Hy/* ch6DataManagement66 */ = {_:0,a:_Hx/* FormStructure.Chapter6.ch6DataManagement67 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Hz/* ch6DataManagement59 */ = new T2(5,_Hy/* FormStructure.Chapter6.ch6DataManagement66 */,_Hv/* FormStructure.Chapter6.ch6DataManagement60 */),
_HA/* ch6DataManagement20 */ = new T2(1,_Hz/* FormStructure.Chapter6.ch6DataManagement59 */,_Hp/* FormStructure.Chapter6.ch6DataManagement21 */),
_HB/* ch6DataManagement72 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you manage versioning?"));
}),
_HC/* ch6DataManagement71 */ = new T1(1,_HB/* FormStructure.Chapter6.ch6DataManagement72 */),
_HD/* ch6DataManagement70 */ = {_:0,a:_HC/* FormStructure.Chapter6.ch6DataManagement71 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_HE/* ch6DataManagement69 */ = new T2(5,_HD/* FormStructure.Chapter6.ch6DataManagement70 */,_Hv/* FormStructure.Chapter6.ch6DataManagement60 */),
_HF/* ch6DataManagement19 */ = new T2(1,_HE/* FormStructure.Chapter6.ch6DataManagement69 */,_HA/* FormStructure.Chapter6.ch6DataManagement20 */),
_HG/* ch6DataManagement76 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Do you handle error reports?"));
}),
_HH/* ch6DataManagement75 */ = new T1(1,_HG/* FormStructure.Chapter6.ch6DataManagement76 */),
_HI/* ch6DataManagement74 */ = {_:0,a:_HH/* FormStructure.Chapter6.ch6DataManagement75 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_HJ/* ch6DataManagement73 */ = new T2(5,_HI/* FormStructure.Chapter6.ch6DataManagement74 */,_Hv/* FormStructure.Chapter6.ch6DataManagement60 */),
_HK/* ch6DataManagement18 */ = new T2(1,_HJ/* FormStructure.Chapter6.ch6DataManagement73 */,_HF/* FormStructure.Chapter6.ch6DataManagement19 */),
_HL/* ch6DataManagement79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Management details"));
}),
_HM/* ch6DataManagement78 */ = new T1(1,_HL/* FormStructure.Chapter6.ch6DataManagement79 */),
_HN/* ch6DataManagement77 */ = {_:0,a:_HM/* FormStructure.Chapter6.ch6DataManagement78 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_HO/* ch6DataManagement17 */ = new T3(8,_HN/* FormStructure.Chapter6.ch6DataManagement77 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_HK/* FormStructure.Chapter6.ch6DataManagement18 */),
_HP/* ch6DataManagement4 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_HQ/* ch6DataManagement16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Total cost of data management"));
}),
_HR/* ch6DataManagement15 */ = new T1(1,_HQ/* FormStructure.Chapter6.ch6DataManagement16 */),
_HS/* ch6DataManagement14 */ = {_:0,a:_HR/* FormStructure.Chapter6.ch6DataManagement15 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_HT/* ch6DataManagement12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("For year 2015"));
}),
_HU/* ch6DataManagement11 */ = new T1(1,_HT/* FormStructure.Chapter6.ch6DataManagement12 */),
_HV/* ch6DataManagement10 */ = {_:0,a:_HU/* FormStructure.Chapter6.ch6DataManagement11 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_HW/* ch6DataManagement9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("thousand EUR"));
}),
_HX/* ch6DataManagement8 */ = new T1(0,_HW/* FormStructure.Chapter6.ch6DataManagement9 */),
_HY/* ch6DataManagement7 */ = new T2(3,_HV/* FormStructure.Chapter6.ch6DataManagement10 */,_HX/* FormStructure.Chapter6.ch6DataManagement8 */),
_HZ/* ch6DataManagement6 */ = new T2(1,_HY/* FormStructure.Chapter6.ch6DataManagement7 */,_I/* GHC.Types.[] */),
_I0/* ch6DataManagement5 */ = new T3(8,_HS/* FormStructure.Chapter6.ch6DataManagement14 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_HZ/* FormStructure.Chapter6.ch6DataManagement6 */),
_I1/* ch6DataManagement3 */ = new T2(1,_I0/* FormStructure.Chapter6.ch6DataManagement5 */,_HP/* FormStructure.Chapter6.ch6DataManagement4 */),
_I2/* ch6DataManagement2 */ = new T2(1,_HO/* FormStructure.Chapter6.ch6DataManagement17 */,_I1/* FormStructure.Chapter6.ch6DataManagement3 */),
_I3/* ch6DataManagement86 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("community use"));
}),
_I4/* ch6DataManagement85 */ = new T1(1,_I3/* FormStructure.Chapter6.ch6DataManagement86 */),
_I5/* ch6DataManagement84 */ = {_:0,a:_I4/* FormStructure.Chapter6.ch6DataManagement85 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_I6/* ch6DataManagement83 */ = new T3(9,_I5/* FormStructure.Chapter6.ch6DataManagement84 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_I7/* ch6DataManagement82 */ = new T2(1,_I6/* FormStructure.Chapter6.ch6DataManagement83 */,_I/* GHC.Types.[] */),
_I8/* ch6DataManagement90 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("local use"));
}),
_I9/* ch6DataManagement89 */ = new T1(1,_I8/* FormStructure.Chapter6.ch6DataManagement90 */),
_Ia/* ch6DataManagement88 */ = {_:0,a:_I9/* FormStructure.Chapter6.ch6DataManagement89 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ib/* ch6DataManagement87 */ = new T3(9,_Ia/* FormStructure.Chapter6.ch6DataManagement88 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_I/* GHC.Types.[] */),
_Ic/* ch6DataManagement81 */ = new T2(1,_Ib/* FormStructure.Chapter6.ch6DataManagement87 */,_I7/* FormStructure.Chapter6.ch6DataManagement82 */),
_Id/* ch6DataManagement93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("We perform data management for:"));
}),
_Ie/* ch6DataManagement92 */ = new T1(1,_Id/* FormStructure.Chapter6.ch6DataManagement93 */),
_If/* ch6DataManagement91 */ = {_:0,a:_Ie/* FormStructure.Chapter6.ch6DataManagement92 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Ig/* ch6DataManagement80 */ = new T3(8,_If/* FormStructure.Chapter6.ch6DataManagement91 */,_GJ/* FormStructure.Chapter6.ch6DataManagement13 */,_Ic/* FormStructure.Chapter6.ch6DataManagement81 */),
_Ih/* ch6DataManagement1 */ = new T2(1,_Ig/* FormStructure.Chapter6.ch6DataManagement80 */,_I2/* FormStructure.Chapter6.ch6DataManagement2 */),
_Ii/* ch6DataManagement96 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("6.Management "));
}),
_Ij/* ch6DataManagement95 */ = new T1(1,_Ii/* FormStructure.Chapter6.ch6DataManagement96 */),
_Ik/* ch6DataManagement94 */ = {_:0,a:_Ij/* FormStructure.Chapter6.ch6DataManagement95 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Il/* ch6DataManagement */ = new T2(7,_Ik/* FormStructure.Chapter6.ch6DataManagement94 */,_Ih/* FormStructure.Chapter6.ch6DataManagement1 */),
_Im/* ch7Roles2 */ = new T2(1,_aG/* FormStructure.Common.remark */,_I/* GHC.Types.[] */),
_In/* ch7Roles13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Full-time equivalent"));
}),
_Io/* ch7Roles12 */ = new T1(0,_In/* FormStructure.Chapter7.ch7Roles13 */),
_Ip/* ch7Roles16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Haste[\'toRoles\']()"));
}),
_Iq/* ch7Roles15 */ = new T1(1,_Ip/* FormStructure.Chapter7.ch7Roles16 */),
_Ir/* ch7Roles27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_Is/* ch7Roles36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_It/* ch7Roles26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_Iu/* ch7Roles59 */ = new T2(1,_It/* FormStructure.Chapter7.ch7Roles26 */,_I/* GHC.Types.[] */),
_Iv/* ch7Roles58 */ = new T2(1,_Is/* FormStructure.Chapter7.ch7Roles36 */,_Iu/* FormStructure.Chapter7.ch7Roles59 */),
_Iw/* ch7Roles57 */ = new T2(1,_Ir/* FormStructure.Chapter7.ch7Roles27 */,_Iv/* FormStructure.Chapter7.ch7Roles58 */),
_Ix/* ch7Roles61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data expert"));
}),
_Iy/* ch7Roles60 */ = new T1(1,_Ix/* FormStructure.Chapter7.ch7Roles61 */),
_Iz/* ch7Roles56 */ = {_:0,a:_Iy/* FormStructure.Chapter7.ch7Roles60 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Iw/* FormStructure.Chapter7.ch7Roles57 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_IA/* ch7Roles55 */ = new T2(3,_Iz/* FormStructure.Chapter7.ch7Roles56 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_IB/* ch7Roles52 */ = new T2(1,_Is/* FormStructure.Chapter7.ch7Roles36 */,_I/* GHC.Types.[] */),
_IC/* ch7Roles54 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data consumer"));
}),
_ID/* ch7Roles53 */ = new T1(1,_IC/* FormStructure.Chapter7.ch7Roles54 */),
_IE/* ch7Roles51 */ = {_:0,a:_ID/* FormStructure.Chapter7.ch7Roles53 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_IB/* FormStructure.Chapter7.ch7Roles52 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_IF/* ch7Roles50 */ = new T2(3,_IE/* FormStructure.Chapter7.ch7Roles51 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_IG/* ch7Roles23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_IH/* ch7Roles22 */ = new T2(1,_IG/* FormStructure.Chapter7.ch7Roles23 */,_I/* GHC.Types.[] */),
_II/* ch7Roles24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_IJ/* ch7Roles21 */ = new T2(1,_II/* FormStructure.Chapter7.ch7Roles24 */,_IH/* FormStructure.Chapter7.ch7Roles22 */),
_IK/* ch7Roles25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_IL/* ch7Roles20 */ = new T2(1,_IK/* FormStructure.Chapter7.ch7Roles25 */,_IJ/* FormStructure.Chapter7.ch7Roles21 */),
_IM/* ch7Roles19 */ = new T2(1,_It/* FormStructure.Chapter7.ch7Roles26 */,_IL/* FormStructure.Chapter7.ch7Roles20 */),
_IN/* ch7Roles35 */ = new T2(1,_Is/* FormStructure.Chapter7.ch7Roles36 */,_IM/* FormStructure.Chapter7.ch7Roles19 */),
_IO/* ch7Roles34 */ = new T2(1,_Ir/* FormStructure.Chapter7.ch7Roles27 */,_IN/* FormStructure.Chapter7.ch7Roles35 */),
_IP/* ch7Roles49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data curator"));
}),
_IQ/* ch7Roles48 */ = new T1(1,_IP/* FormStructure.Chapter7.ch7Roles49 */),
_IR/* ch7Roles47 */ = {_:0,a:_IQ/* FormStructure.Chapter7.ch7Roles48 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_IO/* FormStructure.Chapter7.ch7Roles34 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_IS/* ch7Roles46 */ = new T2(3,_IR/* FormStructure.Chapter7.ch7Roles47 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_IT/* ch7Roles43 */ = new T2(1,_II/* FormStructure.Chapter7.ch7Roles24 */,_I/* GHC.Types.[] */),
_IU/* ch7Roles42 */ = new T2(1,_IK/* FormStructure.Chapter7.ch7Roles25 */,_IT/* FormStructure.Chapter7.ch7Roles43 */),
_IV/* ch7Roles41 */ = new T2(1,_It/* FormStructure.Chapter7.ch7Roles26 */,_IU/* FormStructure.Chapter7.ch7Roles42 */),
_IW/* ch7Roles45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data custodian"));
}),
_IX/* ch7Roles44 */ = new T1(1,_IW/* FormStructure.Chapter7.ch7Roles45 */),
_IY/* ch7Roles40 */ = {_:0,a:_IX/* FormStructure.Chapter7.ch7Roles44 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_IV/* FormStructure.Chapter7.ch7Roles41 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_IZ/* ch7Roles39 */ = new T2(3,_IY/* FormStructure.Chapter7.ch7Roles40 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_J0/* ch7Roles18 */ = new T2(1,_Ir/* FormStructure.Chapter7.ch7Roles27 */,_IM/* FormStructure.Chapter7.ch7Roles19 */),
_J1/* ch7Roles28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_J2/* ch7Roles17 */ = new T2(1,_J1/* FormStructure.Chapter7.ch7Roles28 */,_J0/* FormStructure.Chapter7.ch7Roles18 */),
_J3/* ch7Roles30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data manager"));
}),
_J4/* ch7Roles29 */ = new T1(1,_J3/* FormStructure.Chapter7.ch7Roles30 */),
_J5/* ch7Roles14 */ = {_:0,a:_J4/* FormStructure.Chapter7.ch7Roles29 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_J2/* FormStructure.Chapter7.ch7Roles17 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_J6/* ch7Roles11 */ = new T2(3,_J5/* FormStructure.Chapter7.ch7Roles14 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_J7/* ch7Roles10 */ = new T2(1,_J6/* FormStructure.Chapter7.ch7Roles11 */,_I/* GHC.Types.[] */),
_J8/* ch7Roles33 */ = new T2(1,_J1/* FormStructure.Chapter7.ch7Roles28 */,_IO/* FormStructure.Chapter7.ch7Roles34 */),
_J9/* ch7Roles38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data steward"));
}),
_Ja/* ch7Roles37 */ = new T1(1,_J9/* FormStructure.Chapter7.ch7Roles38 */),
_Jb/* ch7Roles32 */ = {_:0,a:_Ja/* FormStructure.Chapter7.ch7Roles37 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_J8/* FormStructure.Chapter7.ch7Roles33 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Jc/* ch7Roles31 */ = new T2(3,_Jb/* FormStructure.Chapter7.ch7Roles32 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_Jd/* ch7Roles9 */ = new T2(1,_Jc/* FormStructure.Chapter7.ch7Roles31 */,_J7/* FormStructure.Chapter7.ch7Roles10 */),
_Je/* ch7Roles8 */ = new T2(1,_IZ/* FormStructure.Chapter7.ch7Roles39 */,_Jd/* FormStructure.Chapter7.ch7Roles9 */),
_Jf/* ch7Roles7 */ = new T2(1,_IS/* FormStructure.Chapter7.ch7Roles46 */,_Je/* FormStructure.Chapter7.ch7Roles8 */),
_Jg/* ch7Roles6 */ = new T2(1,_IF/* FormStructure.Chapter7.ch7Roles50 */,_Jf/* FormStructure.Chapter7.ch7Roles7 */),
_Jh/* ch7Roles5 */ = new T2(1,_IA/* FormStructure.Chapter7.ch7Roles55 */,_Jg/* FormStructure.Chapter7.ch7Roles6 */),
_Ji/* ch7Roles64 */ = new T2(1,_J1/* FormStructure.Chapter7.ch7Roles28 */,_I/* GHC.Types.[] */),
_Jj/* ch7Roles66 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Data producer"));
}),
_Jk/* ch7Roles65 */ = new T1(1,_Jj/* FormStructure.Chapter7.ch7Roles66 */),
_Jl/* ch7Roles63 */ = {_:0,a:_Jk/* FormStructure.Chapter7.ch7Roles65 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_Ji/* FormStructure.Chapter7.ch7Roles64 */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_Iq/* FormStructure.Chapter7.ch7Roles15 */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Jm/* ch7Roles62 */ = new T2(3,_Jl/* FormStructure.Chapter7.ch7Roles63 */,_Io/* FormStructure.Chapter7.ch7Roles12 */),
_Jn/* ch7Roles4 */ = new T2(1,_Jm/* FormStructure.Chapter7.ch7Roles62 */,_Jh/* FormStructure.Chapter7.ch7Roles5 */),
_Jo/* ch7Roles67 */ = 0,
_Jp/* ch7Roles70 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Employed roles"));
}),
_Jq/* ch7Roles69 */ = new T1(1,_Jp/* FormStructure.Chapter7.ch7Roles70 */),
_Jr/* ch7Roles68 */ = {_:0,a:_Jq/* FormStructure.Chapter7.ch7Roles69 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_Js/* ch7Roles3 */ = new T3(8,_Jr/* FormStructure.Chapter7.ch7Roles68 */,_Jo/* FormStructure.Chapter7.ch7Roles67 */,_Jn/* FormStructure.Chapter7.ch7Roles4 */),
_Jt/* ch7Roles1 */ = new T2(1,_Js/* FormStructure.Chapter7.ch7Roles3 */,_Im/* FormStructure.Chapter7.ch7Roles2 */),
_Ju/* ch7Roles73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("7.Roles "));
}),
_Jv/* ch7Roles72 */ = new T1(1,_Ju/* FormStructure.Chapter7.ch7Roles73 */),
_Jw/* ch7Roles71 */ = {_:0,a:_Jv/* FormStructure.Chapter7.ch7Roles72 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_Jx/* ch7Roles */ = new T2(7,_Jw/* FormStructure.Chapter7.ch7Roles71 */,_Jt/* FormStructure.Chapter7.ch7Roles1 */),
_Jy/* submitForm5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save your answers."));
}),
_Jz/* submitForm4 */ = new T1(1,_Jy/* FormStructure.Submit.submitForm5 */),
_JA/* submitForm3 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_Jz/* FormStructure.Submit.submitForm4 */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_aC/* GHC.Types.True */,i:_I/* GHC.Types.[] */},
_JB/* submitForm2 */ = new T1(11,_JA/* FormStructure.Submit.submitForm3 */),
_JC/* submitForm1 */ = new T2(1,_JB/* FormStructure.Submit.submitForm2 */,_I/* GHC.Types.[] */),
_JD/* submitForm8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Finish"));
}),
_JE/* submitForm7 */ = new T1(1,_JD/* FormStructure.Submit.submitForm8 */),
_JF/* submitForm6 */ = {_:0,a:_JE/* FormStructure.Submit.submitForm7 */,b:_av/* FormEngine.FormItem.NoNumbering */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_JG/* submitForm */ = new T2(7,_JF/* FormStructure.Submit.submitForm6 */,_JC/* FormStructure.Submit.submitForm1 */),
_JH/* formItems9 */ = new T2(1,_JG/* FormStructure.Submit.submitForm */,_I/* GHC.Types.[] */),
_JI/* formItems8 */ = new T2(1,_Jx/* FormStructure.Chapter7.ch7Roles */,_JH/* FormStructure.FormStructure.formItems9 */),
_JJ/* formItems7 */ = new T2(1,_Il/* FormStructure.Chapter6.ch6DataManagement */,_JI/* FormStructure.FormStructure.formItems8 */),
_JK/* formItems6 */ = new T2(1,_GI/* FormStructure.Chapter5.ch5DataAccessibility */,_JJ/* FormStructure.FormStructure.formItems7 */),
_JL/* formItems5 */ = new T2(1,_G8/* FormStructure.Chapter4.ch4DataStorage */,_JK/* FormStructure.FormStructure.formItems6 */),
_JM/* formItems4 */ = new T2(1,_EF/* FormStructure.Chapter3.ch3DataUsage */,_JL/* FormStructure.FormStructure.formItems5 */),
_JN/* formItems3 */ = new T2(1,_Ae/* FormStructure.Chapter2.ch2DataProcessing */,_JM/* FormStructure.FormStructure.formItems4 */),
_JO/* formItems2 */ = new T2(1,_vW/* FormStructure.Chapter1.ch1DataProduction */,_JN/* FormStructure.FormStructure.formItems3 */),
_JP/* formItems1 */ = new T2(1,_rU/* FormStructure.Chapter0.ch0GeneralInformation */,_JO/* FormStructure.FormStructure.formItems2 */),
_JQ/* prepareForm_xs */ = new T(function(){
  return new T2(1,_8o/* FormEngine.FormItem.$fShowNumbering2 */,_JQ/* FormEngine.FormItem.prepareForm_xs */);
}),
_JR/* prepareForm1 */ = new T2(1,_JQ/* FormEngine.FormItem.prepareForm_xs */,_8o/* FormEngine.FormItem.$fShowNumbering2 */),
_JS/* formItems */ = new T(function(){
  return E(B(_ak/* FormEngine.FormItem.$wgo1 */(_JP/* FormStructure.FormStructure.formItems1 */, _JR/* FormEngine.FormItem.prepareForm1 */, _I/* GHC.Types.[] */)).b);
}),
_JT/* $fHasChildrenFormElement_go */ = function(_JU/*  s5UP */, _JV/*  s5UQ */){
  while(1){
    var _JW/*  $fHasChildrenFormElement_go */ = B((function(_JX/* s5UP */, _JY/* s5UQ */){
      var _JZ/* s5UR */ = E(_JX/* s5UP */);
      if(!_JZ/* s5UR */._){
        return E(_JY/* s5UQ */);
      }else{
        var _K0/*   s5UQ */ = B(_12/* GHC.Base.++ */(_JY/* s5UQ */, new T(function(){
          var _K1/* s5UU */ = E(_JZ/* s5UR */.a);
          if(!_K1/* s5UU */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_K1/* s5UU */.c);
          }
        },1)));
        _JU/*  s5UP */ = _JZ/* s5UR */.b;
        _JV/*  s5UQ */ = _K0/*   s5UQ */;
        return __continue/* EXTERNAL */;
      }
    })(_JU/*  s5UP */, _JV/*  s5UQ */));
    if(_JW/*  $fHasChildrenFormElement_go */!=__continue/* EXTERNAL */){
      return _JW/*  $fHasChildrenFormElement_go */;
    }
  }
},
_K2/* $fHasChildrenFormElement_$cchildren */ = function(_K3/* s5V2 */){
  var _K4/* s5V3 */ = E(_K3/* s5V2 */);
  switch(_K4/* s5V3 */._){
    case 0:
      return E(_K4/* s5V3 */.b);
    case 6:
      return new F(function(){return _JT/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_go */(_K4/* s5V3 */.b, _I/* GHC.Types.[] */);});
      break;
    case 8:
      return E(_K4/* s5V3 */.b);
    case 9:
      return E(_K4/* s5V3 */.c);
    case 10:
      return E(_K4/* s5V3 */.b);
    default:
      return __Z/* EXTERNAL */;
  }
},
_K5/* addClass2 */ = "(function (cls, jq) { jq.addClass(cls); return jq; })",
_K6/* $wa */ = function(_K7/* so16 */, _K8/* so17 */, _/* EXTERNAL */){
  var _K9/* so1h */ = eval/* EXTERNAL */(E(_K5/* FormEngine.JQuery.addClass2 */));
  return new F(function(){return E(_K9/* so1h */)(toJSStr/* EXTERNAL */(E(_K7/* so16 */)), _K8/* so17 */);});
},
_Ka/* disableJq5 */ = "(function (k, v, jq) { jq.attr(k, v); return jq; })",
_Kb/* $wa6 */ = function(_Kc/* so2l */, _Kd/* so2m */, _Ke/* so2n */, _/* EXTERNAL */){
  var _Kf/* so2C */ = eval/* EXTERNAL */(E(_Ka/* FormEngine.JQuery.disableJq5 */));
  return new F(function(){return E(_Kf/* so2C */)(toJSStr/* EXTERNAL */(E(_Kc/* so2l */)), toJSStr/* EXTERNAL */(E(_Kd/* so2m */)), _Ke/* so2n */);});
},
_Kg/* addClassInside_f1 */ = new T(function(){
  return (function (jq) { return jq.parent(); });
}),
_Kh/* addClassInside_f2 */ = new T(function(){
  return (function (jq) { return jq.last(); });
}),
_Ki/* addClassInside_f3 */ = new T(function(){
  return (function (jq) { return jq.children(); });
}),
_Kj/* $wa20 */ = function(_Kk/* so2U */, _Kl/* so2V */, _Km/* so2W */, _/* EXTERNAL */){
  var _Kn/* so31 */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_Km/* so2W */),
  _Ko/* so37 */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_Kn/* so31 */),
  _Kp/* so3a */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_Kk/* so2U */, _Kl/* so2V */, _Ko/* so37 */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_Kp/* so3a */));});
},
_Kq/* $wa24 */ = function(_Kr/* so4b */, _Ks/* so4c */, _Kt/* so4d */, _/* EXTERNAL */){
  var _Ku/* so4i */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_Kt/* so4d */),
  _Kv/* so4o */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_Ku/* so4i */),
  _Kw/* so4r */ = B(_77/* FormEngine.JQuery.$wa2 */(_Kr/* so4b */, _Ks/* so4c */, _Kv/* so4o */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_Kw/* so4r */));});
},
_Kx/* appendT2 */ = "(function (tag, jq) { return jq.append(tag); })",
_Ky/* $wa3 */ = function(_Kz/* so06 */, _KA/* so07 */, _/* EXTERNAL */){
  var _KB/* so0h */ = eval/* EXTERNAL */(E(_Kx/* FormEngine.JQuery.appendT2 */));
  return new F(function(){return E(_KB/* so0h */)(toJSStr/* EXTERNAL */(E(_Kz/* so06 */)), _KA/* so07 */);});
},
_KC/* setText2 */ = "(function (txt, jq) { jq.text(txt); return jq; })",
_KD/* $wa34 */ = function(_KE/* so6Y */, _KF/* so6Z */, _/* EXTERNAL */){
  var _KG/* so74 */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_KF/* so6Z */),
  _KH/* so7a */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_KG/* so74 */),
  _KI/* so7l */ = eval/* EXTERNAL */(E(_KC/* FormEngine.JQuery.setText2 */)),
  _KJ/* so7t */ = E(_KI/* so7l */)(toJSStr/* EXTERNAL */(E(_KE/* so6Y */)), _KH/* so7a */);
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(_KJ/* so7t */);});
},
_KK/* appendJq_f1 */ = new T(function(){
  return (function (jq, toJq) { return toJq.append(jq); });
}),
_KL/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<ul>"));
}),
_KM/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("nav"));
}),
_KN/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<li>"));
}),
_KO/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_KP/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<a>"));
}),
_KQ/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'stripe stripe-thin\'>"));
}),
_KR/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_KS/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_KT/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("class"));
}),
_KU/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("inside-bordered"));
}),
_KV/* onClick2 */ = "(function (ev, jq) { jq.click(ev); })",
_KW/* onClick1 */ = function(_KX/* snFB */, _KY/* snFC */, _/* EXTERNAL */){
  var _KZ/* snFO */ = __createJSFunc/* EXTERNAL */(2, function(_L0/* snFF */, _/* EXTERNAL */){
    var _L1/* snFH */ = B(A2(E(_KX/* snFB */),_L0/* snFF */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _L2/* snFR */ = E(_KY/* snFC */),
  _L3/* snFW */ = eval/* EXTERNAL */(E(_KV/* FormEngine.JQuery.onClick2 */)),
  _L4/* snG4 */ = E(_L3/* snFW */)(_KZ/* snFO */, _L2/* snFR */);
  return _L2/* snFR */;
},
_L5/* paneId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("pane_"));
}),
_L6/* paneId */ = function(_L7/* skDz */){
  return new F(function(){return _12/* GHC.Base.++ */(_L5/* FormEngine.FormElement.Identifiers.paneId1 */, new T(function(){
    return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_L7/* skDz */)))).b));
  },1));});
},
_L8/* tabId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("tab_"));
}),
_L9/* tabId */ = function(_La/* skDM */){
  return new F(function(){return _12/* GHC.Base.++ */(_L8/* FormEngine.FormElement.Identifiers.tabId1 */, new T(function(){
    return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_La/* skDM */)))).b));
  },1));});
},
_Lb/* tabName */ = function(_Lc/* skBy */){
  var _Ld/* skBK */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_Lc/* skBy */)))).a);
  return (_Ld/* skBK */._==0) ? __Z/* EXTERNAL */ : E(_Ld/* skBK */.a);
},
_Le/* appearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("block"));
}),
_Lf/* appearJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("display"));
}),
_Lg/* eqString */ = function(_Lh/* s3mQ */, _Li/* s3mR */){
  while(1){
    var _Lj/* s3mS */ = E(_Lh/* s3mQ */);
    if(!_Lj/* s3mS */._){
      return (E(_Li/* s3mR */)._==0) ? true : false;
    }else{
      var _Lk/* s3mY */ = E(_Li/* s3mR */);
      if(!_Lk/* s3mY */._){
        return false;
      }else{
        if(E(_Lj/* s3mS */.a)!=E(_Lk/* s3mY */.a)){
          return false;
        }else{
          _Lh/* s3mQ */ = _Lj/* s3mS */.b;
          _Li/* s3mR */ = _Lk/* s3mY */.b;
          continue;
        }
      }
    }
  }
},
_Ll/* $fEqFormElement_$c== */ = function(_Lm/* s5Uf */, _Ln/* s5Ug */){
  return new F(function(){return _Lg/* GHC.Base.eqString */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_Lm/* s5Uf */)))).b)), B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_Ln/* s5Ug */)))).b)));});
},
_Lo/* removeClass2 */ = "(function (cls, jq) { jq.removeClass(cls); return jq; })",
_Lp/* $wa16 */ = function(_Lq/* so0B */, _Lr/* so0C */, _/* EXTERNAL */){
  var _Ls/* so0M */ = eval/* EXTERNAL */(E(_Lo/* FormEngine.JQuery.removeClass2 */));
  return new F(function(){return E(_Ls/* so0M */)(toJSStr/* EXTERNAL */(E(_Lq/* so0B */)), _Lr/* so0C */);});
},
_Lt/* colorizeTabs2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("notcurrent"));
}),
_Lu/* colorizeTabs3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("current"));
}),
_Lv/* colorizeTabs4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_Lw/* colorizeTabs1 */ = function(_Lx/* slYv */, _Ly/* slYw */, _/* EXTERNAL */){
  var _Lz/* slYy */ = function(_LA/*  slYz */, _/* EXTERNAL */){
    while(1){
      var _LB/*  slYy */ = B((function(_LC/* slYz */, _/* EXTERNAL */){
        var _LD/* slYB */ = E(_LC/* slYz */);
        if(!_LD/* slYB */._){
          return _0/* GHC.Tuple.() */;
        }else{
          var _LE/* slYC */ = _LD/* slYB */.a,
          _LF/* slYD */ = _LD/* slYB */.b;
          if(!B(_Ll/* FormEngine.FormElement.FormElement.$fEqFormElement_$c== */(_LE/* slYC */, _Lx/* slYv */))){
            var _LG/* slYH */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_Lv/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_L9/* FormEngine.FormElement.Identifiers.tabId */(_LE/* slYC */));
            },1))), _/* EXTERNAL */)),
            _LH/* slYM */ = B(_Lp/* FormEngine.JQuery.$wa16 */(_Lu/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_LG/* slYH */), _/* EXTERNAL */)),
            _LI/* slYR */ = B(_K6/* FormEngine.JQuery.$wa */(_Lt/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_LH/* slYM */), _/* EXTERNAL */));
            _LA/*  slYz */ = _LF/* slYD */;
            return __continue/* EXTERNAL */;
          }else{
            var _LJ/* slYW */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_Lv/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
              return B(_L9/* FormEngine.FormElement.Identifiers.tabId */(_LE/* slYC */));
            },1))), _/* EXTERNAL */)),
            _LK/* slZ1 */ = B(_Lp/* FormEngine.JQuery.$wa16 */(_Lt/* FormEngine.FormElement.Tabs.colorizeTabs2 */, E(_LJ/* slYW */), _/* EXTERNAL */)),
            _LL/* slZ6 */ = B(_K6/* FormEngine.JQuery.$wa */(_Lu/* FormEngine.FormElement.Tabs.colorizeTabs3 */, E(_LK/* slZ1 */), _/* EXTERNAL */));
            _LA/*  slYz */ = _LF/* slYD */;
            return __continue/* EXTERNAL */;
          }
        }
      })(_LA/*  slYz */, _/* EXTERNAL */));
      if(_LB/*  slYy */!=__continue/* EXTERNAL */){
        return _LB/*  slYy */;
      }
    }
  };
  return new F(function(){return _Lz/* slYy */(_Ly/* slYw */, _/* EXTERNAL */);});
},
_LM/* disappearJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("none"));
}),
_LN/* toTab2 */ = function(_LO/* slZn */, _/* EXTERNAL */){
  while(1){
    var _LP/* slZp */ = E(_LO/* slZn */);
    if(!_LP/* slZp */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _LQ/* slZu */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, E(_LP/* slZp */.a), _/* EXTERNAL */));
      _LO/* slZn */ = _LP/* slZp */.b;
      continue;
    }
  }
},
_LR/* toTab3 */ = function(_LS/* slZ9 */, _/* EXTERNAL */){
  var _LT/* slZb */ = E(_LS/* slZ9 */);
  if(!_LT/* slZb */._){
    return _I/* GHC.Types.[] */;
  }else{
    var _LU/* slZg */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_Lv/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
      return B(_L6/* FormEngine.FormElement.Identifiers.paneId */(_LT/* slZb */.a));
    },1))), _/* EXTERNAL */)),
    _LV/* slZj */ = B(_LR/* FormEngine.FormElement.Tabs.toTab3 */(_LT/* slZb */.b, _/* EXTERNAL */));
    return new T2(1,_LU/* slZg */,_LV/* slZj */);
  }
},
_LW/* toTab1 */ = function(_LX/* slZx */, _LY/* slZy */, _/* EXTERNAL */){
  var _LZ/* slZC */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_Lv/* FormEngine.FormElement.Tabs.colorizeTabs4 */, new T(function(){
    return B(_L6/* FormEngine.FormElement.Identifiers.paneId */(_LX/* slZx */));
  },1))), _/* EXTERNAL */)),
  _M0/* slZF */ = B(_LR/* FormEngine.FormElement.Tabs.toTab3 */(_LY/* slZy */, _/* EXTERNAL */)),
  _M1/* slZI */ = B(_Lw/* FormEngine.FormElement.Tabs.colorizeTabs1 */(_LX/* slZx */, _LY/* slZy */, _/* EXTERNAL */)),
  _M2/* slZL */ = B(_LN/* FormEngine.FormElement.Tabs.toTab2 */(_M0/* slZF */, _/* EXTERNAL */)),
  _M3/* slZQ */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _Le/* FormEngine.JQuery.appearJq2 */, E(_LZ/* slZC */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_M4/* $wa */ = function(_M5/* slZT */, _M6/* slZU */, _M7/* slZV */, _/* EXTERNAL */){
  var _M8/* slZX */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KL/* FormEngine.FormElement.Tabs.lvl */, _M7/* slZV */, _/* EXTERNAL */)),
  _M9/* sm02 */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
  _Ma/* sm05 */ = __app1/* EXTERNAL */(_M9/* sm02 */, E(_M8/* slZX */)),
  _Mb/* sm08 */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
  _Mc/* sm0b */ = __app1/* EXTERNAL */(_Mb/* sm08 */, _Ma/* sm05 */),
  _Md/* sm0e */ = B(_K6/* FormEngine.JQuery.$wa */(_KM/* FormEngine.FormElement.Tabs.lvl1 */, _Mc/* sm0b */, _/* EXTERNAL */)),
  _Me/* sm0h */ = function(_/* EXTERNAL */, _Mf/* sm0j */){
    var _Mg/* sm0p */ = __app1/* EXTERNAL */(E(_Kg/* FormEngine.JQuery.addClassInside_f1 */), E(_Mf/* sm0j */)),
    _Mh/* sm0s */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KQ/* FormEngine.FormElement.Tabs.lvl5 */, _Mg/* sm0p */, _/* EXTERNAL */)),
    _Mi/* sm0v */ = E(_M5/* slZT */);
    if(!_Mi/* sm0v */._){
      return _Mh/* sm0s */;
    }else{
      var _Mj/* sm0y */ = E(_M6/* slZU */);
      if(!_Mj/* sm0y */._){
        return _Mh/* sm0s */;
      }else{
        var _Mk/* sm0B */ = B(A1(_Mj/* sm0y */.a,_/* EXTERNAL */)),
        _Ml/* sm0I */ = E(_KK/* FormEngine.JQuery.appendJq_f1 */),
        _Mm/* sm0L */ = __app2/* EXTERNAL */(_Ml/* sm0I */, E(_Mk/* sm0B */), E(_Mh/* sm0s */)),
        _Mn/* sm0P */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KO/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
          return B(_L6/* FormEngine.FormElement.Identifiers.paneId */(_Mi/* sm0v */.a));
        },1), _Mm/* sm0L */, _/* EXTERNAL */)),
        _Mo/* sm0U */ = B(_Kq/* FormEngine.JQuery.$wa24 */(_KR/* FormEngine.FormElement.Tabs.lvl6 */, _KS/* FormEngine.FormElement.Tabs.lvl7 */, E(_Mn/* sm0P */), _/* EXTERNAL */)),
        _Mp/* sm0Z */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KT/* FormEngine.FormElement.Tabs.lvl8 */, _KU/* FormEngine.FormElement.Tabs.lvl9 */, E(_Mo/* sm0U */), _/* EXTERNAL */)),
        _Mq/* sm12 */ = function(_Mr/*  sm13 */, _Ms/*  sm14 */, _Mt/*  sm15 */, _/* EXTERNAL */){
          while(1){
            var _Mu/*  sm12 */ = B((function(_Mv/* sm13 */, _Mw/* sm14 */, _Mx/* sm15 */, _/* EXTERNAL */){
              var _My/* sm17 */ = E(_Mv/* sm13 */);
              if(!_My/* sm17 */._){
                return _Mx/* sm15 */;
              }else{
                var _Mz/* sm1a */ = E(_Mw/* sm14 */);
                if(!_Mz/* sm1a */._){
                  return _Mx/* sm15 */;
                }else{
                  var _MA/* sm1d */ = B(A1(_Mz/* sm1a */.a,_/* EXTERNAL */)),
                  _MB/* sm1l */ = __app2/* EXTERNAL */(_Ml/* sm0I */, E(_MA/* sm1d */), E(_Mx/* sm15 */)),
                  _MC/* sm1p */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KO/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
                    return B(_L6/* FormEngine.FormElement.Identifiers.paneId */(_My/* sm17 */.a));
                  },1), _MB/* sm1l */, _/* EXTERNAL */)),
                  _MD/* sm1u */ = B(_Kq/* FormEngine.JQuery.$wa24 */(_KR/* FormEngine.FormElement.Tabs.lvl6 */, _KS/* FormEngine.FormElement.Tabs.lvl7 */, E(_MC/* sm1p */), _/* EXTERNAL */)),
                  _ME/* sm1z */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KT/* FormEngine.FormElement.Tabs.lvl8 */, _KU/* FormEngine.FormElement.Tabs.lvl9 */, E(_MD/* sm1u */), _/* EXTERNAL */));
                  _Mr/*  sm13 */ = _My/* sm17 */.b;
                  _Ms/*  sm14 */ = _Mz/* sm1a */.b;
                  _Mt/*  sm15 */ = _ME/* sm1z */;
                  return __continue/* EXTERNAL */;
                }
              }
            })(_Mr/*  sm13 */, _Ms/*  sm14 */, _Mt/*  sm15 */, _/* EXTERNAL */));
            if(_Mu/*  sm12 */!=__continue/* EXTERNAL */){
              return _Mu/*  sm12 */;
            }
          }
        };
        return new F(function(){return _Mq/* sm12 */(_Mi/* sm0v */.b, _Mj/* sm0y */.b, _Mp/* sm0Z */, _/* EXTERNAL */);});
      }
    }
  },
  _MF/* sm1C */ = E(_M5/* slZT */);
  if(!_MF/* sm1C */._){
    return new F(function(){return _Me/* sm0h */(_/* EXTERNAL */, _Md/* sm0e */);});
  }else{
    var _MG/* sm1D */ = _MF/* sm1C */.a,
    _MH/* sm1H */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KN/* FormEngine.FormElement.Tabs.lvl2 */, E(_Md/* sm0e */), _/* EXTERNAL */)),
    _MI/* sm1N */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KO/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
      return B(_L9/* FormEngine.FormElement.Identifiers.tabId */(_MG/* sm1D */));
    },1), E(_MH/* sm1H */), _/* EXTERNAL */)),
    _MJ/* sm1T */ = __app1/* EXTERNAL */(_M9/* sm02 */, E(_MI/* sm1N */)),
    _MK/* sm1X */ = __app1/* EXTERNAL */(_Mb/* sm08 */, _MJ/* sm1T */),
    _ML/* sm20 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KP/* FormEngine.FormElement.Tabs.lvl4 */, _MK/* sm1X */, _/* EXTERNAL */)),
    _MM/* sm26 */ = B(_KW/* FormEngine.JQuery.onClick1 */(function(_MN/* sm23 */, _/* EXTERNAL */){
      return new F(function(){return _LW/* FormEngine.FormElement.Tabs.toTab1 */(_MG/* sm1D */, _MF/* sm1C */, _/* EXTERNAL */);});
    }, _ML/* sm20 */, _/* EXTERNAL */)),
    _MO/* sm2c */ = B(_KD/* FormEngine.JQuery.$wa34 */(new T(function(){
      return B(_Lb/* FormEngine.FormElement.Identifiers.tabName */(_MG/* sm1D */));
    },1), E(_MM/* sm26 */), _/* EXTERNAL */)),
    _MP/* sm2h */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
    _MQ/* sm2k */ = __app1/* EXTERNAL */(_MP/* sm2h */, E(_MO/* sm2c */)),
    _MR/* sm2n */ = function(_MS/*  sm2o */, _MT/*  sm2p */, _MU/*  slUl */, _/* EXTERNAL */){
      while(1){
        var _MV/*  sm2n */ = B((function(_MW/* sm2o */, _MX/* sm2p */, _MY/* slUl */, _/* EXTERNAL */){
          var _MZ/* sm2r */ = E(_MW/* sm2o */);
          if(!_MZ/* sm2r */._){
            return _MX/* sm2p */;
          }else{
            var _N0/* sm2t */ = _MZ/* sm2r */.a,
            _N1/* sm2v */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KN/* FormEngine.FormElement.Tabs.lvl2 */, _MX/* sm2p */, _/* EXTERNAL */)),
            _N2/* sm2B */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_KO/* FormEngine.FormElement.Tabs.lvl3 */, new T(function(){
              return B(_L9/* FormEngine.FormElement.Identifiers.tabId */(_N0/* sm2t */));
            },1), E(_N1/* sm2v */), _/* EXTERNAL */)),
            _N3/* sm2H */ = __app1/* EXTERNAL */(_M9/* sm02 */, E(_N2/* sm2B */)),
            _N4/* sm2L */ = __app1/* EXTERNAL */(_Mb/* sm08 */, _N3/* sm2H */),
            _N5/* sm2O */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_KP/* FormEngine.FormElement.Tabs.lvl4 */, _N4/* sm2L */, _/* EXTERNAL */)),
            _N6/* sm2U */ = B(_KW/* FormEngine.JQuery.onClick1 */(function(_N7/* sm2R */, _/* EXTERNAL */){
              return new F(function(){return _LW/* FormEngine.FormElement.Tabs.toTab1 */(_N0/* sm2t */, _MF/* sm1C */, _/* EXTERNAL */);});
            }, _N5/* sm2O */, _/* EXTERNAL */)),
            _N8/* sm30 */ = B(_KD/* FormEngine.JQuery.$wa34 */(new T(function(){
              return B(_Lb/* FormEngine.FormElement.Identifiers.tabName */(_N0/* sm2t */));
            },1), E(_N6/* sm2U */), _/* EXTERNAL */)),
            _N9/* sm36 */ = __app1/* EXTERNAL */(_MP/* sm2h */, E(_N8/* sm30 */)),
            _Na/*   slUl */ = _/* EXTERNAL */;
            _MS/*  sm2o */ = _MZ/* sm2r */.b;
            _MT/*  sm2p */ = _N9/* sm36 */;
            _MU/*  slUl */ = _Na/*   slUl */;
            return __continue/* EXTERNAL */;
          }
        })(_MS/*  sm2o */, _MT/*  sm2p */, _MU/*  slUl */, _/* EXTERNAL */));
        if(_MV/*  sm2n */!=__continue/* EXTERNAL */){
          return _MV/*  sm2n */;
        }
      }
    },
    _Nb/* sm39 */ = B(_MR/* sm2n */(_MF/* sm1C */.b, _MQ/* sm2k */, _/* EXTERNAL */, _/* EXTERNAL */));
    return new F(function(){return _Me/* sm0h */(_/* EXTERNAL */, _Nb/* sm39 */);});
  }
},
_Nc/* mouseleave2 */ = "(function (jq) { jq.mouseleave(); })",
_Nd/* $wa14 */ = function(_Ne/* snHi */, _/* EXTERNAL */){
  var _Nf/* snHn */ = eval/* EXTERNAL */(E(_Nc/* FormEngine.JQuery.mouseleave2 */)),
  _Ng/* snHv */ = E(_Nf/* snHn */)(_Ne/* snHi */);
  return _Ne/* snHi */;
},
_Nh/* setHtml2 */ = "(function (html, jq) { jq.html(html); return jq; })",
_Ni/* $wa26 */ = function(_Nj/* so5h */, _Nk/* so5i */, _/* EXTERNAL */){
  var _Nl/* so5s */ = eval/* EXTERNAL */(E(_Nh/* FormEngine.JQuery.setHtml2 */));
  return new F(function(){return E(_Nl/* so5s */)(toJSStr/* EXTERNAL */(E(_Nj/* so5h */)), _Nk/* so5i */);});
},
_Nm/* onLoad2 */ = "(function (ev, jq) { jq[0].addEventListener(\'load\', ev); })",
_Nn/* onLoad1 */ = function(_No/* snBg */, _Np/* snBh */, _/* EXTERNAL */){
  var _Nq/* snBt */ = __createJSFunc/* EXTERNAL */(2, function(_Nr/* snBk */, _/* EXTERNAL */){
    var _Ns/* snBm */ = B(A2(E(_No/* snBg */),_Nr/* snBk */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _Nt/* snBw */ = E(_Np/* snBh */),
  _Nu/* snBB */ = eval/* EXTERNAL */(E(_Nm/* FormEngine.JQuery.onLoad2 */)),
  _Nv/* snBJ */ = E(_Nu/* snBB */)(_Nq/* snBt */, _Nt/* snBw */);
  return _Nt/* snBw */;
},
_Nw/* $wa29 */ = function(_Nx/* snRd */, _Ny/* snRe */, _/* EXTERNAL */){
  var _Nz/* snRj */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_Ny/* snRe */),
  _NA/* snRp */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_Nz/* snRj */),
  _NB/* snRt */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_Nx/* snRd */, _NA/* snRp */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_NB/* snRt */));});
},
_NC/* click2 */ = "(function (jq) { jq.click(); })",
_ND/* $wa5 */ = function(_NE/* snIs */, _/* EXTERNAL */){
  var _NF/* snIx */ = eval/* EXTERNAL */(E(_NC/* FormEngine.JQuery.click2 */)),
  _NG/* snIF */ = E(_NF/* snIx */)(_NE/* snIs */);
  return _NE/* snIs */;
},
_NH/* aboutTab4 */ = 0,
_NI/* aboutTab6 */ = 1000,
_NJ/* aboutTab5 */ = new T2(1,_NI/* Form.aboutTab6 */,_I/* GHC.Types.[] */),
_NK/* aboutTab3 */ = new T2(1,_NJ/* Form.aboutTab5 */,_NH/* Form.aboutTab4 */),
_NL/* aboutTab8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("About"));
}),
_NM/* aboutTab7 */ = new T1(1,_NL/* Form.aboutTab8 */),
_NN/* aboutTab2 */ = {_:0,a:_NM/* Form.aboutTab7 */,b:_NK/* Form.aboutTab3 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_NO/* aboutTab1 */ = new T2(7,_NN/* Form.aboutTab2 */,_I/* GHC.Types.[] */),
_NP/* aboutTab */ = new T3(0,_NO/* Form.aboutTab1 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_NQ/* aboutTabPaneJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("  <div>    <p>      This questionnaire aims to collect managerial information about the bioinformatics data space.    </p>    <p>      <strong>Only data where the respondent is the owner are subject of the questionnaires</strong>, i.e. not data produced as a service.    </p>    <p>      Its completion should take no more than 15 minutes. If you do not know exact answer, provide your best qualified guess.    </p>    <p>      For questions please contact <a href=\'mailto:robert.pergl@fit.cvut.cz\'>robert.pergl@fit.cvut.cz</a>.    </p>    <br>    <p style=\'font-size: 90%; font-style: italic;\'>      Version of this questionnaire: v2.0    </p>  </div> "));
}),
_NR/* aboutTabPaneJq1 */ = function(_/* EXTERNAL */){
  return new F(function(){return _7v/* FormEngine.JQuery.select1 */(_NQ/* Form.aboutTabPaneJq2 */, _/* EXTERNAL */);});
},
_NS/* descSubpaneParagraphId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_desc-subpane-text"));
}),
_NT/* descSubpaneParagraphId */ = function(_NU/* skDZ */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(B(_7g/* FormEngine.FormElement.FormElement.elemChapter */(_NU/* skDZ */)))))).b)), _NS/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId1 */);});
},
_NV/* diagramId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("diagram_"));
}),
_NW/* diagramId */ = function(_NX/* skDl */){
  return new F(function(){return _12/* GHC.Base.++ */(_NV/* FormEngine.FormElement.Identifiers.diagramId1 */, new T(function(){
    return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(B(_7g/* FormEngine.FormElement.FormElement.elemChapter */(_NX/* skDl */)))))).b));
  },1));});
},
_NY/* $fEqOption_$c== */ = function(_NZ/* s5A8 */, _O0/* s5A9 */){
  var _O1/* s5Aa */ = E(_NZ/* s5A8 */);
  if(!_O1/* s5Aa */._){
    var _O2/* s5Ab */ = _O1/* s5Aa */.a,
    _O3/* s5Ac */ = E(_O0/* s5A9 */);
    if(!_O3/* s5Ac */._){
      return new F(function(){return _Lg/* GHC.Base.eqString */(_O2/* s5Ab */, _O3/* s5Ac */.a);});
    }else{
      return new F(function(){return _Lg/* GHC.Base.eqString */(_O2/* s5Ab */, _O3/* s5Ac */.b);});
    }
  }else{
    var _O4/* s5Ai */ = _O1/* s5Aa */.b,
    _O5/* s5Ak */ = E(_O0/* s5A9 */);
    if(!_O5/* s5Ak */._){
      return new F(function(){return _Lg/* GHC.Base.eqString */(_O4/* s5Ai */, _O5/* s5Ak */.a);});
    }else{
      return new F(function(){return _Lg/* GHC.Base.eqString */(_O4/* s5Ai */, _O5/* s5Ak */.b);});
    }
  }
},
_O6/* lvl57 */ = new T2(1,_4q/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_O7/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("IntValueRule (Int -> Bool)"));
}),
_O8/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ReadOnlyRule"));
}),
_O9/* shows_$cshowList */ = function(_Oa/* sff6 */, _Ob/* sff7 */){
  return new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
    return B(_6A/* GHC.Show.showLitString */(_Oa/* sff6 */, new T2(1,_4q/* GHC.Show.shows5 */,_Ob/* sff7 */)));
  }));
},
_Oc/* $fShowFormRule_$cshow */ = function(_Od/* s5zq */){
  var _Oe/* s5zr */ = E(_Od/* s5zq */);
  switch(_Oe/* s5zr */._){
    case 0:
      var _Of/* s5zy */ = new T(function(){
        var _Og/* s5zx */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
            return B(_6A/* GHC.Show.showLitString */(_Oe/* s5zr */.b, _O6/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_O9/* GHC.Show.shows_$cshowList */, _Oe/* s5zr */.a, _I/* GHC.Types.[] */)), _Og/* s5zx */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumRule @ ", _Of/* s5zy */);});
      break;
    case 1:
      var _Oh/* s5zF */ = new T(function(){
        var _Oi/* s5zE */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
            return B(_6A/* GHC.Show.showLitString */(_Oe/* s5zr */.b, _O6/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(B(_26/* GHC.Show.showList__ */(_O9/* GHC.Show.shows_$cshowList */, _Oe/* s5zr */.a, _I/* GHC.Types.[] */)), _Oi/* s5zE */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("SumTBsRule @ ", _Oh/* s5zF */);});
      break;
    case 2:
      var _Oj/* s5zN */ = new T(function(){
        var _Ok/* s5zM */ = new T(function(){
          return B(unAppCStr/* EXTERNAL */(" -> ", new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
            return B(_6A/* GHC.Show.showLitString */(_Oe/* s5zr */.b, _O6/* FormEngine.FormItem.lvl57 */));
          }))));
        },1);
        return B(_12/* GHC.Base.++ */(new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
          return B(_6A/* GHC.Show.showLitString */(_Oe/* s5zr */.a, _O6/* FormEngine.FormItem.lvl57 */));
        })), _Ok/* s5zM */));
      });
      return new F(function(){return unAppCStr/* EXTERNAL */("CopyValueRule @ ", _Oj/* s5zN */);});
      break;
    case 3:
      return E(_O8/* FormEngine.FormItem.lvl7 */);
    default:
      return E(_O7/* FormEngine.FormItem.lvl6 */);
  }
},
_Ol/* identity2element' */ = function(_Om/* sobc */, _On/* sobd */){
  var _Oo/* sobe */ = E(_On/* sobd */);
  if(!_Oo/* sobe */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Op/* sobf */ = _Oo/* sobe */.a,
    _Oq/* sobs */ = function(_Or/* sobt */){
      var _Os/* sobv */ = B(_Ol/* FormEngine.FormElement.Updating.identity2element' */(_Om/* sobc */, B(_K2/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_Op/* sobf */))));
      if(!_Os/* sobv */._){
        return new F(function(){return _Ol/* FormEngine.FormElement.Updating.identity2element' */(_Om/* sobc */, _Oo/* sobe */.b);});
      }else{
        return E(_Os/* sobv */);
      }
    },
    _Ot/* sobx */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_Op/* sobf */)))).c);
    if(!_Ot/* sobx */._){
      if(!B(_Lg/* GHC.Base.eqString */(_I/* GHC.Types.[] */, _Om/* sobc */))){
        return new F(function(){return _Oq/* sobs */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Op/* sobf */);
      }
    }else{
      if(!B(_Lg/* GHC.Base.eqString */(_Ot/* sobx */.a, _Om/* sobc */))){
        return new F(function(){return _Oq/* sobs */(_/* EXTERNAL */);});
      }else{
        return new T1(1,_Op/* sobf */);
      }
    }
  }
},
_Ou/* getRadioValue2 */ = "(function (elId) { return $(elId); })",
_Ov/* getRadioValue3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\']:checked"));
}),
_Ow/* getRadioValue4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("[name=\'"));
}),
_Ox/* getRadioValue1 */ = function(_Oy/* snXa */, _/* EXTERNAL */){
  var _Oz/* snXl */ = eval/* EXTERNAL */(E(_Ou/* FormEngine.JQuery.getRadioValue2 */)),
  _OA/* snXt */ = E(_Oz/* snXl */)(toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Ow/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_Oy/* snXa */, _Ov/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _OB/* snXz */ = E(_3S/* FormEngine.JQuery.getRadioValue_f1 */)(_OA/* snXt */);
  return new T(function(){
    var _OC/* snXD */ = String/* EXTERNAL */(_OB/* snXz */);
    return fromJSStr/* EXTERNAL */(_OC/* snXD */);
  });
},
_OD/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("undefined"));
}),
_OE/* nfiUnitId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_unit"));
}),
_OF/* readEither6 */ = function(_OG/*  s2Rf3 */){
  while(1){
    var _OH/*  readEither6 */ = B((function(_OI/* s2Rf3 */){
      var _OJ/* s2Rf4 */ = E(_OI/* s2Rf3 */);
      if(!_OJ/* s2Rf4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _OK/* s2Rf6 */ = _OJ/* s2Rf4 */.b,
        _OL/* s2Rf7 */ = E(_OJ/* s2Rf4 */.a);
        if(!E(_OL/* s2Rf7 */.b)._){
          return new T2(1,_OL/* s2Rf7 */.a,new T(function(){
            return B(_OF/* Text.Read.readEither6 */(_OK/* s2Rf6 */));
          }));
        }else{
          _OG/*  s2Rf3 */ = _OK/* s2Rf6 */;
          return __continue/* EXTERNAL */;
        }
      }
    })(_OG/*  s2Rf3 */));
    if(_OH/*  readEither6 */!=__continue/* EXTERNAL */){
      return _OH/*  readEither6 */;
    }
  }
},
_OM/* run */ = function(_ON/*  s1iAI */, _OO/*  s1iAJ */){
  while(1){
    var _OP/*  run */ = B((function(_OQ/* s1iAI */, _OR/* s1iAJ */){
      var _OS/* s1iAK */ = E(_OQ/* s1iAI */);
      switch(_OS/* s1iAK */._){
        case 0:
          var _OT/* s1iAM */ = E(_OR/* s1iAJ */);
          if(!_OT/* s1iAM */._){
            return __Z/* EXTERNAL */;
          }else{
            _ON/*  s1iAI */ = B(A1(_OS/* s1iAK */.a,_OT/* s1iAM */.a));
            _OO/*  s1iAJ */ = _OT/* s1iAM */.b;
            return __continue/* EXTERNAL */;
          }
          break;
        case 1:
          var _OU/*   s1iAI */ = B(A1(_OS/* s1iAK */.a,_OR/* s1iAJ */)),
          _OV/*   s1iAJ */ = _OR/* s1iAJ */;
          _ON/*  s1iAI */ = _OU/*   s1iAI */;
          _OO/*  s1iAJ */ = _OV/*   s1iAJ */;
          return __continue/* EXTERNAL */;
        case 2:
          return __Z/* EXTERNAL */;
        case 3:
          return new T2(1,new T2(0,_OS/* s1iAK */.a,_OR/* s1iAJ */),new T(function(){
            return B(_OM/* Text.ParserCombinators.ReadP.run */(_OS/* s1iAK */.b, _OR/* s1iAJ */));
          }));
        default:
          return E(_OS/* s1iAK */.a);
      }
    })(_ON/*  s1iAI */, _OO/*  s1iAJ */));
    if(_OP/*  run */!=__continue/* EXTERNAL */){
      return _OP/*  run */;
    }
  }
},
_OW/* selectByName2 */ = "(function (name) { return $(\'[name=\"\' + name + \'\"]\'); })",
_OX/* selectByName1 */ = function(_OY/* snUw */, _/* EXTERNAL */){
  var _OZ/* snUG */ = eval/* EXTERNAL */(E(_OW/* FormEngine.JQuery.selectByName2 */));
  return new F(function(){return E(_OZ/* snUG */)(toJSStr/* EXTERNAL */(E(_OY/* snUw */)));});
},
_P0/* $fExceptionNestedAtomically_ww2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("base"));
}),
_P1/* $fExceptionNestedAtomically_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Control.Exception.Base"));
}),
_P2/* $fExceptionPatternMatchFail_ww5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PatternMatchFail"));
}),
_P3/* $fExceptionPatternMatchFail_wild */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_P0/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_P1/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_P2/* Control.Exception.Base.$fExceptionPatternMatchFail_ww5 */),
_P4/* $fExceptionPatternMatchFail2 */ = new T5(0,new Long/* EXTERNAL */(18445595, 3739165398, true),new Long/* EXTERNAL */(52003073, 3246954884, true),_P3/* Control.Exception.Base.$fExceptionPatternMatchFail_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_P5/* $fExceptionPatternMatchFail1 */ = function(_P6/* s4nv1 */){
  return E(_P4/* Control.Exception.Base.$fExceptionPatternMatchFail2 */);
},
_P7/* $fExceptionPatternMatchFail_$cfromException */ = function(_P8/* s4nvc */){
  var _P9/* s4nvd */ = E(_P8/* s4nvc */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_P9/* s4nvd */.a)), _P5/* Control.Exception.Base.$fExceptionPatternMatchFail1 */, _P9/* s4nvd */.b);});
},
_Pa/* $fExceptionPatternMatchFail_$cshow */ = function(_Pb/* s4nv4 */){
  return E(E(_Pb/* s4nv4 */).a);
},
_Pc/* $fExceptionPatternMatchFail_$ctoException */ = function(_Pd/* B1 */){
  return new T2(0,_Pe/* Control.Exception.Base.$fExceptionPatternMatchFail */,_Pd/* B1 */);
},
_Pf/* $fShowPatternMatchFail1 */ = function(_Pg/* s4nqK */, _Ph/* s4nqL */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_Pg/* s4nqK */).a, _Ph/* s4nqL */);});
},
_Pi/* $fShowPatternMatchFail_$cshowList */ = function(_Pj/* s4nv2 */, _Pk/* s4nv3 */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_Pf/* Control.Exception.Base.$fShowPatternMatchFail1 */, _Pj/* s4nv2 */, _Pk/* s4nv3 */);});
},
_Pl/* $fShowPatternMatchFail_$cshowsPrec */ = function(_Pm/* s4nv7 */, _Pn/* s4nv8 */, _Po/* s4nv9 */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_Pn/* s4nv8 */).a, _Po/* s4nv9 */);});
},
_Pp/* $fShowPatternMatchFail */ = new T3(0,_Pl/* Control.Exception.Base.$fShowPatternMatchFail_$cshowsPrec */,_Pa/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */,_Pi/* Control.Exception.Base.$fShowPatternMatchFail_$cshowList */),
_Pe/* $fExceptionPatternMatchFail */ = new T(function(){
  return new T5(0,_P5/* Control.Exception.Base.$fExceptionPatternMatchFail1 */,_Pp/* Control.Exception.Base.$fShowPatternMatchFail */,_Pc/* Control.Exception.Base.$fExceptionPatternMatchFail_$ctoException */,_P7/* Control.Exception.Base.$fExceptionPatternMatchFail_$cfromException */,_Pa/* Control.Exception.Base.$fExceptionPatternMatchFail_$cshow */);
}),
_Pq/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Non-exhaustive patterns in"));
}),
_Pr/* lvl */ = function(_Ps/* s2SzX */, _Pt/* s2SzY */){
  return new F(function(){return die/* EXTERNAL */(new T(function(){
    return B(A2(_2m/* GHC.Exception.toException */,_Pt/* s2SzY */, _Ps/* s2SzX */));
  }));});
},
_Pu/* throw1 */ = function(_Pv/* B2 */, _Pw/* B1 */){
  return new F(function(){return _Pr/* GHC.Exception.lvl */(_Pv/* B2 */, _Pw/* B1 */);});
},
_Px/* $wspan */ = function(_Py/* s9vU */, _Pz/* s9vV */){
  var _PA/* s9vW */ = E(_Pz/* s9vV */);
  if(!_PA/* s9vW */._){
    return new T2(0,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */);
  }else{
    var _PB/* s9vX */ = _PA/* s9vW */.a;
    if(!B(A1(_Py/* s9vU */,_PB/* s9vX */))){
      return new T2(0,_I/* GHC.Types.[] */,_PA/* s9vW */);
    }else{
      var _PC/* s9w0 */ = new T(function(){
        var _PD/* s9w1 */ = B(_Px/* GHC.List.$wspan */(_Py/* s9vU */, _PA/* s9vW */.b));
        return new T2(0,_PD/* s9w1 */.a,_PD/* s9w1 */.b);
      });
      return new T2(0,new T2(1,_PB/* s9vX */,new T(function(){
        return E(E(_PC/* s9w0 */).a);
      })),new T(function(){
        return E(E(_PC/* s9w0 */).b);
      }));
    }
  }
},
_PE/* untangle1 */ = 32,
_PF/* untangle2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\n"));
}),
_PG/* untangle3 */ = function(_PH/* s3K4R */){
  return (E(_PH/* s3K4R */)==124) ? false : true;
},
_PI/* untangle */ = function(_PJ/* s3K5K */, _PK/* s3K5L */){
  var _PL/* s3K5N */ = B(_Px/* GHC.List.$wspan */(_PG/* GHC.IO.Exception.untangle3 */, B(unCStr/* EXTERNAL */(_PJ/* s3K5K */)))),
  _PM/* s3K5O */ = _PL/* s3K5N */.a,
  _PN/* s3K5Q */ = function(_PO/* s3K5R */, _PP/* s3K5S */){
    var _PQ/* s3K5V */ = new T(function(){
      var _PR/* s3K5U */ = new T(function(){
        return B(_12/* GHC.Base.++ */(_PK/* s3K5L */, new T(function(){
          return B(_12/* GHC.Base.++ */(_PP/* s3K5S */, _PF/* GHC.IO.Exception.untangle2 */));
        },1)));
      });
      return B(unAppCStr/* EXTERNAL */(": ", _PR/* s3K5U */));
    },1);
    return new F(function(){return _12/* GHC.Base.++ */(_PO/* s3K5R */, _PQ/* s3K5V */);});
  },
  _PS/* s3K5W */ = E(_PL/* s3K5N */.b);
  if(!_PS/* s3K5W */._){
    return new F(function(){return _PN/* s3K5Q */(_PM/* s3K5O */, _I/* GHC.Types.[] */);});
  }else{
    if(E(_PS/* s3K5W */.a)==124){
      return new F(function(){return _PN/* s3K5Q */(_PM/* s3K5O */, new T2(1,_PE/* GHC.IO.Exception.untangle1 */,_PS/* s3K5W */.b));});
    }else{
      return new F(function(){return _PN/* s3K5Q */(_PM/* s3K5O */, _I/* GHC.Types.[] */);});
    }
  }
},
_PT/* patError */ = function(_PU/* s4nwI */){
  return new F(function(){return _Pu/* GHC.Exception.throw1 */(new T1(0,new T(function(){
    return B(_PI/* GHC.IO.Exception.untangle */(_PU/* s4nwI */, _Pq/* Control.Exception.Base.lvl3 */));
  })), _Pe/* Control.Exception.Base.$fExceptionPatternMatchFail */);});
},
_PV/* lvl2 */ = new T(function(){
  return B(_PT/* Control.Exception.Base.patError */("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));
}),
_PW/* $fAlternativeP_$c<|> */ = function(_PX/* s1iBo */, _PY/* s1iBp */){
  var _PZ/* s1iBq */ = function(_Q0/* s1iBr */){
    var _Q1/* s1iBs */ = E(_PY/* s1iBp */);
    if(_Q1/* s1iBs */._==3){
      return new T2(3,_Q1/* s1iBs */.a,new T(function(){
        return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_PX/* s1iBo */, _Q1/* s1iBs */.b));
      }));
    }else{
      var _Q2/* s1iBt */ = E(_PX/* s1iBo */);
      if(_Q2/* s1iBt */._==2){
        return E(_Q1/* s1iBs */);
      }else{
        var _Q3/* s1iBu */ = E(_Q1/* s1iBs */);
        if(_Q3/* s1iBu */._==2){
          return E(_Q2/* s1iBt */);
        }else{
          var _Q4/* s1iBv */ = function(_Q5/* s1iBw */){
            var _Q6/* s1iBx */ = E(_Q3/* s1iBu */);
            if(_Q6/* s1iBx */._==4){
              var _Q7/* s1iBU */ = function(_Q8/* s1iBR */){
                return new T1(4,new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_OM/* Text.ParserCombinators.ReadP.run */(_Q2/* s1iBt */, _Q8/* s1iBR */)), _Q6/* s1iBx */.a));
                }));
              };
              return new T1(1,_Q7/* s1iBU */);
            }else{
              var _Q9/* s1iBy */ = E(_Q2/* s1iBt */);
              if(_Q9/* s1iBy */._==1){
                var _Qa/* s1iBF */ = _Q9/* s1iBy */.a,
                _Qb/* s1iBG */ = E(_Q6/* s1iBx */);
                if(!_Qb/* s1iBG */._){
                  return new T1(1,function(_Qc/* s1iBI */){
                    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_Qa/* s1iBF */,_Qc/* s1iBI */)), _Qb/* s1iBG */);});
                  });
                }else{
                  var _Qd/* s1iBP */ = function(_Qe/* s1iBM */){
                    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_Qa/* s1iBF */,_Qe/* s1iBM */)), new T(function(){
                      return B(A1(_Qb/* s1iBG */.a,_Qe/* s1iBM */));
                    }));});
                  };
                  return new T1(1,_Qd/* s1iBP */);
                }
              }else{
                var _Qf/* s1iBz */ = E(_Q6/* s1iBx */);
                if(!_Qf/* s1iBz */._){
                  return E(_PV/* Text.ParserCombinators.ReadP.lvl2 */);
                }else{
                  var _Qg/* s1iBE */ = function(_Qh/* s1iBC */){
                    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_Q9/* s1iBy */, new T(function(){
                      return B(A1(_Qf/* s1iBz */.a,_Qh/* s1iBC */));
                    }));});
                  };
                  return new T1(1,_Qg/* s1iBE */);
                }
              }
            }
          },
          _Qi/* s1iBV */ = E(_Q2/* s1iBt */);
          switch(_Qi/* s1iBV */._){
            case 1:
              var _Qj/* s1iBX */ = E(_Q3/* s1iBu */);
              if(_Qj/* s1iBX */._==4){
                var _Qk/* s1iC3 */ = function(_Ql/* s1iBZ */){
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_OM/* Text.ParserCombinators.ReadP.run */(B(A1(_Qi/* s1iBV */.a,_Ql/* s1iBZ */)), _Ql/* s1iBZ */)), _Qj/* s1iBX */.a));
                  }));
                };
                return new T1(1,_Qk/* s1iC3 */);
              }else{
                return new F(function(){return _Q4/* s1iBv */(_/* EXTERNAL */);});
              }
              break;
            case 4:
              var _Qm/* s1iC4 */ = _Qi/* s1iBV */.a,
              _Qn/* s1iC5 */ = E(_Q3/* s1iBu */);
              switch(_Qn/* s1iC5 */._){
                case 0:
                  var _Qo/* s1iCa */ = function(_Qp/* s1iC7 */){
                    var _Qq/* s1iC9 */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_Qm/* s1iC4 */, new T(function(){
                        return B(_OM/* Text.ParserCombinators.ReadP.run */(_Qn/* s1iC5 */, _Qp/* s1iC7 */));
                      },1)));
                    });
                    return new T1(4,_Qq/* s1iC9 */);
                  };
                  return new T1(1,_Qo/* s1iCa */);
                case 1:
                  var _Qr/* s1iCg */ = function(_Qs/* s1iCc */){
                    var _Qt/* s1iCf */ = new T(function(){
                      return B(_12/* GHC.Base.++ */(_Qm/* s1iC4 */, new T(function(){
                        return B(_OM/* Text.ParserCombinators.ReadP.run */(B(A1(_Qn/* s1iC5 */.a,_Qs/* s1iCc */)), _Qs/* s1iCc */));
                      },1)));
                    });
                    return new T1(4,_Qt/* s1iCf */);
                  };
                  return new T1(1,_Qr/* s1iCg */);
                default:
                  return new T1(4,new T(function(){
                    return B(_12/* GHC.Base.++ */(_Qm/* s1iC4 */, _Qn/* s1iC5 */.a));
                  }));
              }
              break;
            default:
              return new F(function(){return _Q4/* s1iBv */(_/* EXTERNAL */);});
          }
        }
      }
    }
  },
  _Qu/* s1iCm */ = E(_PX/* s1iBo */);
  switch(_Qu/* s1iCm */._){
    case 0:
      var _Qv/* s1iCo */ = E(_PY/* s1iBp */);
      if(!_Qv/* s1iCo */._){
        var _Qw/* s1iCt */ = function(_Qx/* s1iCq */){
          return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_Qu/* s1iCm */.a,_Qx/* s1iCq */)), new T(function(){
            return B(A1(_Qv/* s1iCo */.a,_Qx/* s1iCq */));
          }));});
        };
        return new T1(0,_Qw/* s1iCt */);
      }else{
        return new F(function(){return _PZ/* s1iBq */(_/* EXTERNAL */);});
      }
      break;
    case 3:
      return new T2(3,_Qu/* s1iCm */.a,new T(function(){
        return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(_Qu/* s1iCm */.b, _PY/* s1iBp */));
      }));
    default:
      return new F(function(){return _PZ/* s1iBq */(_/* EXTERNAL */);});
  }
},
_Qy/* $fRead(,)3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("("));
}),
_Qz/* $fRead(,)4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(")"));
}),
_QA/* $fEqChar_$c/= */ = function(_QB/* scFn */, _QC/* scFo */){
  return E(_QB/* scFn */)!=E(_QC/* scFo */);
},
_QD/* $fEqChar_$c== */ = function(_QE/* scFu */, _QF/* scFv */){
  return E(_QE/* scFu */)==E(_QF/* scFv */);
},
_QG/* $fEqChar */ = new T2(0,_QD/* GHC.Classes.$fEqChar_$c== */,_QA/* GHC.Classes.$fEqChar_$c/= */),
_QH/* $fEq[]_$s$c==1 */ = function(_QI/* scIY */, _QJ/* scIZ */){
  while(1){
    var _QK/* scJ0 */ = E(_QI/* scIY */);
    if(!_QK/* scJ0 */._){
      return (E(_QJ/* scIZ */)._==0) ? true : false;
    }else{
      var _QL/* scJ6 */ = E(_QJ/* scIZ */);
      if(!_QL/* scJ6 */._){
        return false;
      }else{
        if(E(_QK/* scJ0 */.a)!=E(_QL/* scJ6 */.a)){
          return false;
        }else{
          _QI/* scIY */ = _QK/* scJ0 */.b;
          _QJ/* scIZ */ = _QL/* scJ6 */.b;
          continue;
        }
      }
    }
  }
},
_QM/* $fEq[]_$s$c/=1 */ = function(_QN/* scJE */, _QO/* scJF */){
  return (!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_QN/* scJE */, _QO/* scJF */))) ? true : false;
},
_QP/* $fEq[]_$s$fEq[]1 */ = new T2(0,_QH/* GHC.Classes.$fEq[]_$s$c==1 */,_QM/* GHC.Classes.$fEq[]_$s$c/=1 */),
_QQ/* $fAlternativeP_$c>>= */ = function(_QR/* s1iCx */, _QS/* s1iCy */){
  var _QT/* s1iCz */ = E(_QR/* s1iCx */);
  switch(_QT/* s1iCz */._){
    case 0:
      return new T1(0,function(_QU/* s1iCB */){
        return new F(function(){return _QQ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_QT/* s1iCz */.a,_QU/* s1iCB */)), _QS/* s1iCy */);});
      });
    case 1:
      return new T1(1,function(_QV/* s1iCF */){
        return new F(function(){return _QQ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(B(A1(_QT/* s1iCz */.a,_QV/* s1iCF */)), _QS/* s1iCy */);});
      });
    case 2:
      return new T0(2);
    case 3:
      return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_QS/* s1iCy */,_QT/* s1iCz */.a)), new T(function(){
        return B(_QQ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_QT/* s1iCz */.b, _QS/* s1iCy */));
      }));});
      break;
    default:
      var _QW/* s1iCN */ = function(_QX/* s1iCO */){
        var _QY/* s1iCP */ = E(_QX/* s1iCO */);
        if(!_QY/* s1iCP */._){
          return __Z/* EXTERNAL */;
        }else{
          var _QZ/* s1iCS */ = E(_QY/* s1iCP */.a);
          return new F(function(){return _12/* GHC.Base.++ */(B(_OM/* Text.ParserCombinators.ReadP.run */(B(A1(_QS/* s1iCy */,_QZ/* s1iCS */.a)), _QZ/* s1iCS */.b)), new T(function(){
            return B(_QW/* s1iCN */(_QY/* s1iCP */.b));
          },1));});
        }
      },
      _R0/* s1iCY */ = B(_QW/* s1iCN */(_QT/* s1iCz */.a));
      return (_R0/* s1iCY */._==0) ? new T0(2) : new T1(4,_R0/* s1iCY */);
  }
},
_R1/* Fail */ = new T0(2),
_R2/* $fApplicativeP_$creturn */ = function(_R3/* s1iBl */){
  return new T2(3,_R3/* s1iBl */,_R1/* Text.ParserCombinators.ReadP.Fail */);
},
_R4/* <++2 */ = function(_R5/* s1iyp */, _R6/* s1iyq */){
  var _R7/* s1iyr */ = E(_R5/* s1iyp */);
  if(!_R7/* s1iyr */){
    return new F(function(){return A1(_R6/* s1iyq */,_0/* GHC.Tuple.() */);});
  }else{
    var _R8/* s1iys */ = new T(function(){
      return B(_R4/* Text.ParserCombinators.ReadP.<++2 */(_R7/* s1iyr */-1|0, _R6/* s1iyq */));
    });
    return new T1(0,function(_R9/* s1iyu */){
      return E(_R8/* s1iys */);
    });
  }
},
_Ra/* $wa */ = function(_Rb/* s1iD8 */, _Rc/* s1iD9 */, _Rd/* s1iDa */){
  var _Re/* s1iDb */ = new T(function(){
    return B(A1(_Rb/* s1iD8 */,_R2/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
  }),
  _Rf/* s1iDc */ = function(_Rg/*  s1iDd */, _Rh/*  s1iDe */, _Ri/*  s1iDf */, _Rj/*  s1iDg */){
    while(1){
      var _Rk/*  s1iDc */ = B((function(_Rl/* s1iDd */, _Rm/* s1iDe */, _Rn/* s1iDf */, _Ro/* s1iDg */){
        var _Rp/* s1iDh */ = E(_Rl/* s1iDd */);
        switch(_Rp/* s1iDh */._){
          case 0:
            var _Rq/* s1iDj */ = E(_Rm/* s1iDe */);
            if(!_Rq/* s1iDj */._){
              return new F(function(){return A1(_Rc/* s1iD9 */,_Ro/* s1iDg */);});
            }else{
              var _Rr/*   s1iDf */ = _Rn/* s1iDf */+1|0,
              _Rs/*   s1iDg */ = _Ro/* s1iDg */;
              _Rg/*  s1iDd */ = B(A1(_Rp/* s1iDh */.a,_Rq/* s1iDj */.a));
              _Rh/*  s1iDe */ = _Rq/* s1iDj */.b;
              _Ri/*  s1iDf */ = _Rr/*   s1iDf */;
              _Rj/*  s1iDg */ = _Rs/*   s1iDg */;
              return __continue/* EXTERNAL */;
            }
            break;
          case 1:
            var _Rt/*   s1iDd */ = B(A1(_Rp/* s1iDh */.a,_Rm/* s1iDe */)),
            _Ru/*   s1iDe */ = _Rm/* s1iDe */,
            _Rr/*   s1iDf */ = _Rn/* s1iDf */,
            _Rs/*   s1iDg */ = _Ro/* s1iDg */;
            _Rg/*  s1iDd */ = _Rt/*   s1iDd */;
            _Rh/*  s1iDe */ = _Ru/*   s1iDe */;
            _Ri/*  s1iDf */ = _Rr/*   s1iDf */;
            _Rj/*  s1iDg */ = _Rs/*   s1iDg */;
            return __continue/* EXTERNAL */;
          case 2:
            return new F(function(){return A1(_Rc/* s1iD9 */,_Ro/* s1iDg */);});
            break;
          case 3:
            var _Rv/* s1iDs */ = new T(function(){
              return B(_QQ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Rp/* s1iDh */, _Ro/* s1iDg */));
            });
            return new F(function(){return _R4/* Text.ParserCombinators.ReadP.<++2 */(_Rn/* s1iDf */, function(_Rw/* s1iDt */){
              return E(_Rv/* s1iDs */);
            });});
            break;
          default:
            return new F(function(){return _QQ/* Text.ParserCombinators.ReadP.$fAlternativeP_$c>>= */(_Rp/* s1iDh */, _Ro/* s1iDg */);});
        }
      })(_Rg/*  s1iDd */, _Rh/*  s1iDe */, _Ri/*  s1iDf */, _Rj/*  s1iDg */));
      if(_Rk/*  s1iDc */!=__continue/* EXTERNAL */){
        return _Rk/*  s1iDc */;
      }
    }
  };
  return function(_Rx/* s1iDw */){
    return new F(function(){return _Rf/* s1iDc */(_Re/* s1iDb */, _Rx/* s1iDw */, 0, _Rd/* s1iDa */);});
  };
},
_Ry/* munch3 */ = function(_Rz/* s1iyo */){
  return new F(function(){return A1(_Rz/* s1iyo */,_I/* GHC.Types.[] */);});
},
_RA/* $wa3 */ = function(_RB/* s1iyQ */, _RC/* s1iyR */){
  var _RD/* s1iyS */ = function(_RE/* s1iyT */){
    var _RF/* s1iyU */ = E(_RE/* s1iyT */);
    if(!_RF/* s1iyU */._){
      return E(_Ry/* Text.ParserCombinators.ReadP.munch3 */);
    }else{
      var _RG/* s1iyV */ = _RF/* s1iyU */.a;
      if(!B(A1(_RB/* s1iyQ */,_RG/* s1iyV */))){
        return E(_Ry/* Text.ParserCombinators.ReadP.munch3 */);
      }else{
        var _RH/* s1iyY */ = new T(function(){
          return B(_RD/* s1iyS */(_RF/* s1iyU */.b));
        }),
        _RI/* s1iz6 */ = function(_RJ/* s1iyZ */){
          var _RK/* s1iz0 */ = new T(function(){
            return B(A1(_RH/* s1iyY */,function(_RL/* s1iz1 */){
              return new F(function(){return A1(_RJ/* s1iyZ */,new T2(1,_RG/* s1iyV */,_RL/* s1iz1 */));});
            }));
          });
          return new T1(0,function(_RM/* s1iz4 */){
            return E(_RK/* s1iz0 */);
          });
        };
        return E(_RI/* s1iz6 */);
      }
    }
  };
  return function(_RN/* s1iz7 */){
    return new F(function(){return A2(_RD/* s1iyS */,_RN/* s1iz7 */, _RC/* s1iyR */);});
  };
},
_RO/* EOF */ = new T0(6),
_RP/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("valDig: Bad base"));
}),
_RQ/* readDecP2 */ = new T(function(){
  return B(err/* EXTERNAL */(_RP/* Text.Read.Lex.lvl37 */));
}),
_RR/* $wa6 */ = function(_RS/* s1oaO */, _RT/* s1oaP */){
  var _RU/* s1oaQ */ = function(_RV/* s1oaR */, _RW/* s1oaS */){
    var _RX/* s1oaT */ = E(_RV/* s1oaR */);
    if(!_RX/* s1oaT */._){
      var _RY/* s1oaU */ = new T(function(){
        return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
      });
      return function(_RZ/* s1oaV */){
        return new F(function(){return A1(_RZ/* s1oaV */,_RY/* s1oaU */);});
      };
    }else{
      var _S0/* s1ob1 */ = E(_RX/* s1oaT */.a),
      _S1/* s1ob3 */ = function(_S2/* s1ob4 */){
        var _S3/* s1ob5 */ = new T(function(){
          return B(_RU/* s1oaQ */(_RX/* s1oaT */.b, function(_S4/* s1ob6 */){
            return new F(function(){return A1(_RW/* s1oaS */,new T2(1,_S2/* s1ob4 */,_S4/* s1ob6 */));});
          }));
        }),
        _S5/* s1obd */ = function(_S6/* s1ob9 */){
          var _S7/* s1oba */ = new T(function(){
            return B(A1(_S3/* s1ob5 */,_S6/* s1ob9 */));
          });
          return new T1(0,function(_S8/* s1obb */){
            return E(_S7/* s1oba */);
          });
        };
        return E(_S5/* s1obd */);
      };
      switch(E(_RS/* s1oaO */)){
        case 8:
          if(48>_S0/* s1ob1 */){
            var _S9/* s1obi */ = new T(function(){
              return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_Sa/* s1obj */){
              return new F(function(){return A1(_Sa/* s1obj */,_S9/* s1obi */);});
            };
          }else{
            if(_S0/* s1ob1 */>55){
              var _Sb/* s1obn */ = new T(function(){
                return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_Sc/* s1obo */){
                return new F(function(){return A1(_Sc/* s1obo */,_Sb/* s1obn */);});
              };
            }else{
              return new F(function(){return _S1/* s1ob3 */(_S0/* s1ob1 */-48|0);});
            }
          }
          break;
        case 10:
          if(48>_S0/* s1ob1 */){
            var _Sd/* s1obv */ = new T(function(){
              return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
            });
            return function(_Se/* s1obw */){
              return new F(function(){return A1(_Se/* s1obw */,_Sd/* s1obv */);});
            };
          }else{
            if(_S0/* s1ob1 */>57){
              var _Sf/* s1obA */ = new T(function(){
                return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
              });
              return function(_Sg/* s1obB */){
                return new F(function(){return A1(_Sg/* s1obB */,_Sf/* s1obA */);});
              };
            }else{
              return new F(function(){return _S1/* s1ob3 */(_S0/* s1ob1 */-48|0);});
            }
          }
          break;
        case 16:
          if(48>_S0/* s1ob1 */){
            if(97>_S0/* s1ob1 */){
              if(65>_S0/* s1ob1 */){
                var _Sh/* s1obM */ = new T(function(){
                  return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                });
                return function(_Si/* s1obN */){
                  return new F(function(){return A1(_Si/* s1obN */,_Sh/* s1obM */);});
                };
              }else{
                if(_S0/* s1ob1 */>70){
                  var _Sj/* s1obR */ = new T(function(){
                    return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_Sk/* s1obS */){
                    return new F(function(){return A1(_Sk/* s1obS */,_Sj/* s1obR */);});
                  };
                }else{
                  return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-65|0)+10|0);});
                }
              }
            }else{
              if(_S0/* s1ob1 */>102){
                if(65>_S0/* s1ob1 */){
                  var _Sl/* s1oc2 */ = new T(function(){
                    return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_Sm/* s1oc3 */){
                    return new F(function(){return A1(_Sm/* s1oc3 */,_Sl/* s1oc2 */);});
                  };
                }else{
                  if(_S0/* s1ob1 */>70){
                    var _Sn/* s1oc7 */ = new T(function(){
                      return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_So/* s1oc8 */){
                      return new F(function(){return A1(_So/* s1oc8 */,_Sn/* s1oc7 */);});
                    };
                  }else{
                    return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-97|0)+10|0);});
              }
            }
          }else{
            if(_S0/* s1ob1 */>57){
              if(97>_S0/* s1ob1 */){
                if(65>_S0/* s1ob1 */){
                  var _Sp/* s1oco */ = new T(function(){
                    return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                  });
                  return function(_Sq/* s1ocp */){
                    return new F(function(){return A1(_Sq/* s1ocp */,_Sp/* s1oco */);});
                  };
                }else{
                  if(_S0/* s1ob1 */>70){
                    var _Sr/* s1oct */ = new T(function(){
                      return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Ss/* s1ocu */){
                      return new F(function(){return A1(_Ss/* s1ocu */,_Sr/* s1oct */);});
                    };
                  }else{
                    return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-65|0)+10|0);});
                  }
                }
              }else{
                if(_S0/* s1ob1 */>102){
                  if(65>_S0/* s1ob1 */){
                    var _St/* s1ocE */ = new T(function(){
                      return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                    });
                    return function(_Su/* s1ocF */){
                      return new F(function(){return A1(_Su/* s1ocF */,_St/* s1ocE */);});
                    };
                  }else{
                    if(_S0/* s1ob1 */>70){
                      var _Sv/* s1ocJ */ = new T(function(){
                        return B(A1(_RW/* s1oaS */,_I/* GHC.Types.[] */));
                      });
                      return function(_Sw/* s1ocK */){
                        return new F(function(){return A1(_Sw/* s1ocK */,_Sv/* s1ocJ */);});
                      };
                    }else{
                      return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-65|0)+10|0);});
                    }
                  }
                }else{
                  return new F(function(){return _S1/* s1ob3 */((_S0/* s1ob1 */-97|0)+10|0);});
                }
              }
            }else{
              return new F(function(){return _S1/* s1ob3 */(_S0/* s1ob1 */-48|0);});
            }
          }
          break;
        default:
          return E(_RQ/* Text.Read.Lex.readDecP2 */);
      }
    }
  },
  _Sx/* s1ocX */ = function(_Sy/* s1ocY */){
    var _Sz/* s1ocZ */ = E(_Sy/* s1ocY */);
    if(!_Sz/* s1ocZ */._){
      return new T0(2);
    }else{
      return new F(function(){return A1(_RT/* s1oaP */,_Sz/* s1ocZ */);});
    }
  };
  return function(_SA/* s1od2 */){
    return new F(function(){return A3(_RU/* s1oaQ */,_SA/* s1od2 */, _4/* GHC.Base.id */, _Sx/* s1ocX */);});
  };
},
_SB/* lvl41 */ = 16,
_SC/* lvl42 */ = 8,
_SD/* $wa7 */ = function(_SE/* s1od4 */){
  var _SF/* s1od5 */ = function(_SG/* s1od6 */){
    return new F(function(){return A1(_SE/* s1od4 */,new T1(5,new T2(0,_SC/* Text.Read.Lex.lvl42 */,_SG/* s1od6 */)));});
  },
  _SH/* s1od9 */ = function(_SI/* s1oda */){
    return new F(function(){return A1(_SE/* s1od4 */,new T1(5,new T2(0,_SB/* Text.Read.Lex.lvl41 */,_SI/* s1oda */)));});
  },
  _SJ/* s1odd */ = function(_SK/* s1ode */){
    switch(E(_SK/* s1ode */)){
      case 79:
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SC/* Text.Read.Lex.lvl42 */, _SF/* s1od5 */)));
      case 88:
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SB/* Text.Read.Lex.lvl41 */, _SH/* s1od9 */)));
      case 111:
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SC/* Text.Read.Lex.lvl42 */, _SF/* s1od5 */)));
      case 120:
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SB/* Text.Read.Lex.lvl41 */, _SH/* s1od9 */)));
      default:
        return new T0(2);
    }
  };
  return function(_SL/* s1odr */){
    return (E(_SL/* s1odr */)==48) ? E(new T1(0,_SJ/* s1odd */)) : new T0(2);
  };
},
_SM/* a2 */ = function(_SN/* s1odw */){
  return new T1(0,B(_SD/* Text.Read.Lex.$wa7 */(_SN/* s1odw */)));
},
_SO/* a */ = function(_SP/* s1o94 */){
  return new F(function(){return A1(_SP/* s1o94 */,_2o/* GHC.Base.Nothing */);});
},
_SQ/* a1 */ = function(_SR/* s1o95 */){
  return new F(function(){return A1(_SR/* s1o95 */,_2o/* GHC.Base.Nothing */);});
},
_SS/* lvl */ = 10,
_ST/* log2I1 */ = new T1(0,1),
_SU/* lvl2 */ = new T1(0,2147483647),
_SV/* plusInteger */ = function(_SW/* s1Qe */, _SX/* s1Qf */){
  while(1){
    var _SY/* s1Qg */ = E(_SW/* s1Qe */);
    if(!_SY/* s1Qg */._){
      var _SZ/* s1Qh */ = _SY/* s1Qg */.a,
      _T0/* s1Qi */ = E(_SX/* s1Qf */);
      if(!_T0/* s1Qi */._){
        var _T1/* s1Qj */ = _T0/* s1Qi */.a,
        _T2/* s1Qk */ = addC/* EXTERNAL */(_SZ/* s1Qh */, _T1/* s1Qj */);
        if(!E(_T2/* s1Qk */.b)){
          return new T1(0,_T2/* s1Qk */.a);
        }else{
          _SW/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_SZ/* s1Qh */));
          _SX/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_T1/* s1Qj */));
          continue;
        }
      }else{
        _SW/* s1Qe */ = new T1(1,I_fromInt/* EXTERNAL */(_SZ/* s1Qh */));
        _SX/* s1Qf */ = _T0/* s1Qi */;
        continue;
      }
    }else{
      var _T3/* s1Qz */ = E(_SX/* s1Qf */);
      if(!_T3/* s1Qz */._){
        _SW/* s1Qe */ = _SY/* s1Qg */;
        _SX/* s1Qf */ = new T1(1,I_fromInt/* EXTERNAL */(_T3/* s1Qz */.a));
        continue;
      }else{
        return new T1(1,I_add/* EXTERNAL */(_SY/* s1Qg */.a, _T3/* s1Qz */.a));
      }
    }
  }
},
_T4/* lvl3 */ = new T(function(){
  return B(_SV/* GHC.Integer.Type.plusInteger */(_SU/* GHC.Integer.Type.lvl2 */, _ST/* GHC.Integer.Type.log2I1 */));
}),
_T5/* negateInteger */ = function(_T6/* s1QH */){
  var _T7/* s1QI */ = E(_T6/* s1QH */);
  if(!_T7/* s1QI */._){
    var _T8/* s1QK */ = E(_T7/* s1QI */.a);
    return (_T8/* s1QK */==(-2147483648)) ? E(_T4/* GHC.Integer.Type.lvl3 */) : new T1(0, -_T8/* s1QK */);
  }else{
    return new T1(1,I_negate/* EXTERNAL */(_T7/* s1QI */.a));
  }
},
_T9/* numberToFixed1 */ = new T1(0,10),
_Ta/* $wlenAcc */ = function(_Tb/* s9Bd */, _Tc/* s9Be */){
  while(1){
    var _Td/* s9Bf */ = E(_Tb/* s9Bd */);
    if(!_Td/* s9Bf */._){
      return E(_Tc/* s9Be */);
    }else{
      var _Te/*  s9Be */ = _Tc/* s9Be */+1|0;
      _Tb/* s9Bd */ = _Td/* s9Bf */.b;
      _Tc/* s9Be */ = _Te/*  s9Be */;
      continue;
    }
  }
},
_Tf/* smallInteger */ = function(_Tg/* B1 */){
  return new T1(0,_Tg/* B1 */);
},
_Th/* numberToFixed2 */ = function(_Ti/* s1o9e */){
  return new F(function(){return _Tf/* GHC.Integer.Type.smallInteger */(E(_Ti/* s1o9e */));});
},
_Tj/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("this should not happen"));
}),
_Tk/* lvl40 */ = new T(function(){
  return B(err/* EXTERNAL */(_Tj/* Text.Read.Lex.lvl39 */));
}),
_Tl/* timesInteger */ = function(_Tm/* s1PN */, _Tn/* s1PO */){
  while(1){
    var _To/* s1PP */ = E(_Tm/* s1PN */);
    if(!_To/* s1PP */._){
      var _Tp/* s1PQ */ = _To/* s1PP */.a,
      _Tq/* s1PR */ = E(_Tn/* s1PO */);
      if(!_Tq/* s1PR */._){
        var _Tr/* s1PS */ = _Tq/* s1PR */.a;
        if(!(imul/* EXTERNAL */(_Tp/* s1PQ */, _Tr/* s1PS */)|0)){
          return new T1(0,imul/* EXTERNAL */(_Tp/* s1PQ */, _Tr/* s1PS */)|0);
        }else{
          _Tm/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Tp/* s1PQ */));
          _Tn/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Tr/* s1PS */));
          continue;
        }
      }else{
        _Tm/* s1PN */ = new T1(1,I_fromInt/* EXTERNAL */(_Tp/* s1PQ */));
        _Tn/* s1PO */ = _Tq/* s1PR */;
        continue;
      }
    }else{
      var _Ts/* s1Q6 */ = E(_Tn/* s1PO */);
      if(!_Ts/* s1Q6 */._){
        _Tm/* s1PN */ = _To/* s1PP */;
        _Tn/* s1PO */ = new T1(1,I_fromInt/* EXTERNAL */(_Ts/* s1Q6 */.a));
        continue;
      }else{
        return new T1(1,I_mul/* EXTERNAL */(_To/* s1PP */.a, _Ts/* s1Q6 */.a));
      }
    }
  }
},
_Tt/* combine */ = function(_Tu/* s1o9h */, _Tv/* s1o9i */){
  var _Tw/* s1o9j */ = E(_Tv/* s1o9i */);
  if(!_Tw/* s1o9j */._){
    return __Z/* EXTERNAL */;
  }else{
    var _Tx/* s1o9m */ = E(_Tw/* s1o9j */.b);
    return (_Tx/* s1o9m */._==0) ? E(_Tk/* Text.Read.Lex.lvl40 */) : new T2(1,B(_SV/* GHC.Integer.Type.plusInteger */(B(_Tl/* GHC.Integer.Type.timesInteger */(_Tw/* s1o9j */.a, _Tu/* s1o9h */)), _Tx/* s1o9m */.a)),new T(function(){
      return B(_Tt/* Text.Read.Lex.combine */(_Tu/* s1o9h */, _Tx/* s1o9m */.b));
    }));
  }
},
_Ty/* numberToFixed3 */ = new T1(0,0),
_Tz/* numberToFixed_go */ = function(_TA/*  s1o9s */, _TB/*  s1o9t */, _TC/*  s1o9u */){
  while(1){
    var _TD/*  numberToFixed_go */ = B((function(_TE/* s1o9s */, _TF/* s1o9t */, _TG/* s1o9u */){
      var _TH/* s1o9v */ = E(_TG/* s1o9u */);
      if(!_TH/* s1o9v */._){
        return E(_Ty/* Text.Read.Lex.numberToFixed3 */);
      }else{
        if(!E(_TH/* s1o9v */.b)._){
          return E(_TH/* s1o9v */.a);
        }else{
          var _TI/* s1o9B */ = E(_TF/* s1o9t */);
          if(_TI/* s1o9B */<=40){
            var _TJ/* s1o9F */ = function(_TK/* s1o9G */, _TL/* s1o9H */){
              while(1){
                var _TM/* s1o9I */ = E(_TL/* s1o9H */);
                if(!_TM/* s1o9I */._){
                  return E(_TK/* s1o9G */);
                }else{
                  var _TN/*  s1o9G */ = B(_SV/* GHC.Integer.Type.plusInteger */(B(_Tl/* GHC.Integer.Type.timesInteger */(_TK/* s1o9G */, _TE/* s1o9s */)), _TM/* s1o9I */.a));
                  _TK/* s1o9G */ = _TN/*  s1o9G */;
                  _TL/* s1o9H */ = _TM/* s1o9I */.b;
                  continue;
                }
              }
            };
            return new F(function(){return _TJ/* s1o9F */(_Ty/* Text.Read.Lex.numberToFixed3 */, _TH/* s1o9v */);});
          }else{
            var _TO/* s1o9N */ = B(_Tl/* GHC.Integer.Type.timesInteger */(_TE/* s1o9s */, _TE/* s1o9s */));
            if(!(_TI/* s1o9B */%2)){
              var _TP/*   s1o9u */ = B(_Tt/* Text.Read.Lex.combine */(_TE/* s1o9s */, _TH/* s1o9v */));
              _TA/*  s1o9s */ = _TO/* s1o9N */;
              _TB/*  s1o9t */ = quot/* EXTERNAL */(_TI/* s1o9B */+1|0, 2);
              _TC/*  s1o9u */ = _TP/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }else{
              var _TP/*   s1o9u */ = B(_Tt/* Text.Read.Lex.combine */(_TE/* s1o9s */, new T2(1,_Ty/* Text.Read.Lex.numberToFixed3 */,_TH/* s1o9v */)));
              _TA/*  s1o9s */ = _TO/* s1o9N */;
              _TB/*  s1o9t */ = quot/* EXTERNAL */(_TI/* s1o9B */+1|0, 2);
              _TC/*  s1o9u */ = _TP/*   s1o9u */;
              return __continue/* EXTERNAL */;
            }
          }
        }
      }
    })(_TA/*  s1o9s */, _TB/*  s1o9t */, _TC/*  s1o9u */));
    if(_TD/*  numberToFixed_go */!=__continue/* EXTERNAL */){
      return _TD/*  numberToFixed_go */;
    }
  }
},
_TQ/* valInteger */ = function(_TR/* s1off */, _TS/* s1ofg */){
  return new F(function(){return _Tz/* Text.Read.Lex.numberToFixed_go */(_TR/* s1off */, new T(function(){
    return B(_Ta/* GHC.List.$wlenAcc */(_TS/* s1ofg */, 0));
  },1), B(_2S/* GHC.Base.map */(_Th/* Text.Read.Lex.numberToFixed2 */, _TS/* s1ofg */)));});
},
_TT/* a26 */ = function(_TU/* s1og4 */){
  var _TV/* s1og5 */ = new T(function(){
    var _TW/* s1ogC */ = new T(function(){
      var _TX/* s1ogz */ = function(_TY/* s1ogw */){
        return new F(function(){return A1(_TU/* s1og4 */,new T1(1,new T(function(){
          return B(_TQ/* Text.Read.Lex.valInteger */(_T9/* Text.Read.Lex.numberToFixed1 */, _TY/* s1ogw */));
        })));});
      };
      return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SS/* Text.Read.Lex.lvl */, _TX/* s1ogz */)));
    }),
    _TZ/* s1ogt */ = function(_U0/* s1ogj */){
      if(E(_U0/* s1ogj */)==43){
        var _U1/* s1ogq */ = function(_U2/* s1ogn */){
          return new F(function(){return A1(_TU/* s1og4 */,new T1(1,new T(function(){
            return B(_TQ/* Text.Read.Lex.valInteger */(_T9/* Text.Read.Lex.numberToFixed1 */, _U2/* s1ogn */));
          })));});
        };
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SS/* Text.Read.Lex.lvl */, _U1/* s1ogq */)));
      }else{
        return new T0(2);
      }
    },
    _U3/* s1ogh */ = function(_U4/* s1og6 */){
      if(E(_U4/* s1og6 */)==45){
        var _U5/* s1oge */ = function(_U6/* s1oga */){
          return new F(function(){return A1(_TU/* s1og4 */,new T1(1,new T(function(){
            return B(_T5/* GHC.Integer.Type.negateInteger */(B(_TQ/* Text.Read.Lex.valInteger */(_T9/* Text.Read.Lex.numberToFixed1 */, _U6/* s1oga */))));
          })));});
        };
        return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SS/* Text.Read.Lex.lvl */, _U5/* s1oge */)));
      }else{
        return new T0(2);
      }
    };
    return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_U3/* s1ogh */), new T1(0,_TZ/* s1ogt */))), _TW/* s1ogC */));
  });
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_U7/* s1ogD */){
    return (E(_U7/* s1ogD */)==101) ? E(_TV/* s1og5 */) : new T0(2);
  }), new T1(0,function(_U8/* s1ogJ */){
    return (E(_U8/* s1ogJ */)==69) ? E(_TV/* s1og5 */) : new T0(2);
  }));});
},
_U9/* $wa8 */ = function(_Ua/* s1odz */){
  var _Ub/* s1odA */ = function(_Uc/* s1odB */){
    return new F(function(){return A1(_Ua/* s1odz */,new T1(1,_Uc/* s1odB */));});
  };
  return function(_Ud/* s1odD */){
    return (E(_Ud/* s1odD */)==46) ? new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_SS/* Text.Read.Lex.lvl */, _Ub/* s1odA */))) : new T0(2);
  };
},
_Ue/* a3 */ = function(_Uf/* s1odK */){
  return new T1(0,B(_U9/* Text.Read.Lex.$wa8 */(_Uf/* s1odK */)));
},
_Ug/* $wa10 */ = function(_Uh/* s1ogP */){
  var _Ui/* s1oh1 */ = function(_Uj/* s1ogQ */){
    var _Uk/* s1ogY */ = function(_Ul/* s1ogR */){
      return new T1(1,B(_Ra/* Text.ParserCombinators.ReadP.$wa */(_TT/* Text.Read.Lex.a26 */, _SO/* Text.Read.Lex.a */, function(_Um/* s1ogS */){
        return new F(function(){return A1(_Uh/* s1ogP */,new T1(5,new T3(1,_Uj/* s1ogQ */,_Ul/* s1ogR */,_Um/* s1ogS */)));});
      })));
    };
    return new T1(1,B(_Ra/* Text.ParserCombinators.ReadP.$wa */(_Ue/* Text.Read.Lex.a3 */, _SQ/* Text.Read.Lex.a1 */, _Uk/* s1ogY */)));
  };
  return new F(function(){return _RR/* Text.Read.Lex.$wa6 */(_SS/* Text.Read.Lex.lvl */, _Ui/* s1oh1 */);});
},
_Un/* a27 */ = function(_Uo/* s1oh2 */){
  return new T1(1,B(_Ug/* Text.Read.Lex.$wa10 */(_Uo/* s1oh2 */)));
},
_Up/* == */ = function(_Uq/* scBJ */){
  return E(E(_Uq/* scBJ */).a);
},
_Ur/* elem */ = function(_Us/* s9uW */, _Ut/* s9uX */, _Uu/* s9uY */){
  while(1){
    var _Uv/* s9uZ */ = E(_Uu/* s9uY */);
    if(!_Uv/* s9uZ */._){
      return false;
    }else{
      if(!B(A3(_Up/* GHC.Classes.== */,_Us/* s9uW */, _Ut/* s9uX */, _Uv/* s9uZ */.a))){
        _Uu/* s9uY */ = _Uv/* s9uZ */.b;
        continue;
      }else{
        return true;
      }
    }
  }
},
_Uw/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("!@#$%&*+./<=>?\\^|:-~"));
}),
_Ux/* a6 */ = function(_Uy/* s1odZ */){
  return new F(function(){return _Ur/* GHC.List.elem */(_QG/* GHC.Classes.$fEqChar */, _Uy/* s1odZ */, _Uw/* Text.Read.Lex.lvl44 */);});
},
_Uz/* $wa9 */ = function(_UA/* s1odN */){
  var _UB/* s1odO */ = new T(function(){
    return B(A1(_UA/* s1odN */,_SC/* Text.Read.Lex.lvl42 */));
  }),
  _UC/* s1odP */ = new T(function(){
    return B(A1(_UA/* s1odN */,_SB/* Text.Read.Lex.lvl41 */));
  });
  return function(_UD/* s1odQ */){
    switch(E(_UD/* s1odQ */)){
      case 79:
        return E(_UB/* s1odO */);
      case 88:
        return E(_UC/* s1odP */);
      case 111:
        return E(_UB/* s1odO */);
      case 120:
        return E(_UC/* s1odP */);
      default:
        return new T0(2);
    }
  };
},
_UE/* a4 */ = function(_UF/* s1odV */){
  return new T1(0,B(_Uz/* Text.Read.Lex.$wa9 */(_UF/* s1odV */)));
},
_UG/* a5 */ = function(_UH/* s1odY */){
  return new F(function(){return A1(_UH/* s1odY */,_SS/* Text.Read.Lex.lvl */);});
},
_UI/* chr2 */ = function(_UJ/* sjTv */){
  return new F(function(){return err/* EXTERNAL */(B(unAppCStr/* EXTERNAL */("Prelude.chr: bad argument: ", new T(function(){
    return B(_4a/* GHC.Show.$wshowSignedInt */(9, _UJ/* sjTv */, _I/* GHC.Types.[] */));
  }))));});
},
_UK/* integerToInt */ = function(_UL/* s1Rv */){
  var _UM/* s1Rw */ = E(_UL/* s1Rv */);
  if(!_UM/* s1Rw */._){
    return E(_UM/* s1Rw */.a);
  }else{
    return new F(function(){return I_toInt/* EXTERNAL */(_UM/* s1Rw */.a);});
  }
},
_UN/* leInteger */ = function(_UO/* s1Gp */, _UP/* s1Gq */){
  var _UQ/* s1Gr */ = E(_UO/* s1Gp */);
  if(!_UQ/* s1Gr */._){
    var _UR/* s1Gs */ = _UQ/* s1Gr */.a,
    _US/* s1Gt */ = E(_UP/* s1Gq */);
    return (_US/* s1Gt */._==0) ? _UR/* s1Gs */<=_US/* s1Gt */.a : I_compareInt/* EXTERNAL */(_US/* s1Gt */.a, _UR/* s1Gs */)>=0;
  }else{
    var _UT/* s1GA */ = _UQ/* s1Gr */.a,
    _UU/* s1GB */ = E(_UP/* s1Gq */);
    return (_UU/* s1GB */._==0) ? I_compareInt/* EXTERNAL */(_UT/* s1GA */, _UU/* s1GB */.a)<=0 : I_compare/* EXTERNAL */(_UT/* s1GA */, _UU/* s1GB */.a)<=0;
  }
},
_UV/* pfail1 */ = function(_UW/* s1izT */){
  return new T0(2);
},
_UX/* choice */ = function(_UY/* s1iDZ */){
  var _UZ/* s1iE0 */ = E(_UY/* s1iDZ */);
  if(!_UZ/* s1iE0 */._){
    return E(_UV/* Text.ParserCombinators.ReadP.pfail1 */);
  }else{
    var _V0/* s1iE1 */ = _UZ/* s1iE0 */.a,
    _V1/* s1iE3 */ = E(_UZ/* s1iE0 */.b);
    if(!_V1/* s1iE3 */._){
      return E(_V0/* s1iE1 */);
    }else{
      var _V2/* s1iE6 */ = new T(function(){
        return B(_UX/* Text.ParserCombinators.ReadP.choice */(_V1/* s1iE3 */));
      }),
      _V3/* s1iEa */ = function(_V4/* s1iE7 */){
        return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_V0/* s1iE1 */,_V4/* s1iE7 */)), new T(function(){
          return B(A1(_V2/* s1iE6 */,_V4/* s1iE7 */));
        }));});
      };
      return E(_V3/* s1iEa */);
    }
  }
},
_V5/* $wa6 */ = function(_V6/* s1izU */, _V7/* s1izV */){
  var _V8/* s1izW */ = function(_V9/* s1izX */, _Va/* s1izY */, _Vb/* s1izZ */){
    var _Vc/* s1iA0 */ = E(_V9/* s1izX */);
    if(!_Vc/* s1iA0 */._){
      return new F(function(){return A1(_Vb/* s1izZ */,_V6/* s1izU */);});
    }else{
      var _Vd/* s1iA3 */ = E(_Va/* s1izY */);
      if(!_Vd/* s1iA3 */._){
        return new T0(2);
      }else{
        if(E(_Vc/* s1iA0 */.a)!=E(_Vd/* s1iA3 */.a)){
          return new T0(2);
        }else{
          var _Ve/* s1iAc */ = new T(function(){
            return B(_V8/* s1izW */(_Vc/* s1iA0 */.b, _Vd/* s1iA3 */.b, _Vb/* s1izZ */));
          });
          return new T1(0,function(_Vf/* s1iAd */){
            return E(_Ve/* s1iAc */);
          });
        }
      }
    }
  };
  return function(_Vg/* s1iAf */){
    return new F(function(){return _V8/* s1izW */(_V6/* s1izU */, _Vg/* s1iAf */, _V7/* s1izV */);});
  };
},
_Vh/* a28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SO"));
}),
_Vi/* lvl29 */ = 14,
_Vj/* a29 */ = function(_Vk/* s1onM */){
  var _Vl/* s1onN */ = new T(function(){
    return B(A1(_Vk/* s1onM */,_Vi/* Text.Read.Lex.lvl29 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Vh/* Text.Read.Lex.a28 */, function(_Vm/* s1onO */){
    return E(_Vl/* s1onN */);
  })));
},
_Vn/* a30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SOH"));
}),
_Vo/* lvl35 */ = 1,
_Vp/* a31 */ = function(_Vq/* s1onS */){
  var _Vr/* s1onT */ = new T(function(){
    return B(A1(_Vq/* s1onS */,_Vo/* Text.Read.Lex.lvl35 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Vn/* Text.Read.Lex.a30 */, function(_Vs/* s1onU */){
    return E(_Vr/* s1onT */);
  })));
},
_Vt/* a32 */ = function(_Vu/* s1onY */){
  return new T1(1,B(_Ra/* Text.ParserCombinators.ReadP.$wa */(_Vp/* Text.Read.Lex.a31 */, _Vj/* Text.Read.Lex.a29 */, _Vu/* s1onY */)));
},
_Vv/* a33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NUL"));
}),
_Vw/* lvl36 */ = 0,
_Vx/* a34 */ = function(_Vy/* s1oo1 */){
  var _Vz/* s1oo2 */ = new T(function(){
    return B(A1(_Vy/* s1oo1 */,_Vw/* Text.Read.Lex.lvl36 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Vv/* Text.Read.Lex.a33 */, function(_VA/* s1oo3 */){
    return E(_Vz/* s1oo2 */);
  })));
},
_VB/* a35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("STX"));
}),
_VC/* lvl34 */ = 2,
_VD/* a36 */ = function(_VE/* s1oo7 */){
  var _VF/* s1oo8 */ = new T(function(){
    return B(A1(_VE/* s1oo7 */,_VC/* Text.Read.Lex.lvl34 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_VB/* Text.Read.Lex.a35 */, function(_VG/* s1oo9 */){
    return E(_VF/* s1oo8 */);
  })));
},
_VH/* a37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETX"));
}),
_VI/* lvl33 */ = 3,
_VJ/* a38 */ = function(_VK/* s1ood */){
  var _VL/* s1ooe */ = new T(function(){
    return B(A1(_VK/* s1ood */,_VI/* Text.Read.Lex.lvl33 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_VH/* Text.Read.Lex.a37 */, function(_VM/* s1oof */){
    return E(_VL/* s1ooe */);
  })));
},
_VN/* a39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EOT"));
}),
_VO/* lvl32 */ = 4,
_VP/* a40 */ = function(_VQ/* s1ooj */){
  var _VR/* s1ook */ = new T(function(){
    return B(A1(_VQ/* s1ooj */,_VO/* Text.Read.Lex.lvl32 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_VN/* Text.Read.Lex.a39 */, function(_VS/* s1ool */){
    return E(_VR/* s1ook */);
  })));
},
_VT/* a41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ENQ"));
}),
_VU/* lvl31 */ = 5,
_VV/* a42 */ = function(_VW/* s1oop */){
  var _VX/* s1ooq */ = new T(function(){
    return B(A1(_VW/* s1oop */,_VU/* Text.Read.Lex.lvl31 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_VT/* Text.Read.Lex.a41 */, function(_VY/* s1oor */){
    return E(_VX/* s1ooq */);
  })));
},
_VZ/* a43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ACK"));
}),
_W0/* lvl30 */ = 6,
_W1/* a44 */ = function(_W2/* s1oov */){
  var _W3/* s1oow */ = new T(function(){
    return B(A1(_W2/* s1oov */,_W0/* Text.Read.Lex.lvl30 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_VZ/* Text.Read.Lex.a43 */, function(_W4/* s1oox */){
    return E(_W3/* s1oow */);
  })));
},
_W5/* a45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BEL"));
}),
_W6/* lvl7 */ = 7,
_W7/* a46 */ = function(_W8/* s1ooB */){
  var _W9/* s1ooC */ = new T(function(){
    return B(A1(_W8/* s1ooB */,_W6/* Text.Read.Lex.lvl7 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_W5/* Text.Read.Lex.a45 */, function(_Wa/* s1ooD */){
    return E(_W9/* s1ooC */);
  })));
},
_Wb/* a47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("BS"));
}),
_Wc/* lvl6 */ = 8,
_Wd/* a48 */ = function(_We/* s1ooH */){
  var _Wf/* s1ooI */ = new T(function(){
    return B(A1(_We/* s1ooH */,_Wc/* Text.Read.Lex.lvl6 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Wb/* Text.Read.Lex.a47 */, function(_Wg/* s1ooJ */){
    return E(_Wf/* s1ooI */);
  })));
},
_Wh/* a49 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("HT"));
}),
_Wi/* lvl2 */ = 9,
_Wj/* a50 */ = function(_Wk/* s1ooN */){
  var _Wl/* s1ooO */ = new T(function(){
    return B(A1(_Wk/* s1ooN */,_Wi/* Text.Read.Lex.lvl2 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Wh/* Text.Read.Lex.a49 */, function(_Wm/* s1ooP */){
    return E(_Wl/* s1ooO */);
  })));
},
_Wn/* a51 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("LF"));
}),
_Wo/* lvl4 */ = 10,
_Wp/* a52 */ = function(_Wq/* s1ooT */){
  var _Wr/* s1ooU */ = new T(function(){
    return B(A1(_Wq/* s1ooT */,_Wo/* Text.Read.Lex.lvl4 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Wn/* Text.Read.Lex.a51 */, function(_Ws/* s1ooV */){
    return E(_Wr/* s1ooU */);
  })));
},
_Wt/* a53 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("VT"));
}),
_Wu/* lvl1 */ = 11,
_Wv/* a54 */ = function(_Ww/* s1ooZ */){
  var _Wx/* s1op0 */ = new T(function(){
    return B(A1(_Ww/* s1ooZ */,_Wu/* Text.Read.Lex.lvl1 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Wt/* Text.Read.Lex.a53 */, function(_Wy/* s1op1 */){
    return E(_Wx/* s1op0 */);
  })));
},
_Wz/* a55 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FF"));
}),
_WA/* lvl5 */ = 12,
_WB/* a56 */ = function(_WC/* s1op5 */){
  var _WD/* s1op6 */ = new T(function(){
    return B(A1(_WC/* s1op5 */,_WA/* Text.Read.Lex.lvl5 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Wz/* Text.Read.Lex.a55 */, function(_WE/* s1op7 */){
    return E(_WD/* s1op6 */);
  })));
},
_WF/* a57 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CR"));
}),
_WG/* lvl3 */ = 13,
_WH/* a58 */ = function(_WI/* s1opb */){
  var _WJ/* s1opc */ = new T(function(){
    return B(A1(_WI/* s1opb */,_WG/* Text.Read.Lex.lvl3 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_WF/* Text.Read.Lex.a57 */, function(_WK/* s1opd */){
    return E(_WJ/* s1opc */);
  })));
},
_WL/* a59 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SI"));
}),
_WM/* lvl28 */ = 15,
_WN/* a60 */ = function(_WO/* s1oph */){
  var _WP/* s1opi */ = new T(function(){
    return B(A1(_WO/* s1oph */,_WM/* Text.Read.Lex.lvl28 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_WL/* Text.Read.Lex.a59 */, function(_WQ/* s1opj */){
    return E(_WP/* s1opi */);
  })));
},
_WR/* a61 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DLE"));
}),
_WS/* lvl27 */ = 16,
_WT/* a62 */ = function(_WU/* s1opn */){
  var _WV/* s1opo */ = new T(function(){
    return B(A1(_WU/* s1opn */,_WS/* Text.Read.Lex.lvl27 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_WR/* Text.Read.Lex.a61 */, function(_WW/* s1opp */){
    return E(_WV/* s1opo */);
  })));
},
_WX/* a63 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC1"));
}),
_WY/* lvl26 */ = 17,
_WZ/* a64 */ = function(_X0/* s1opt */){
  var _X1/* s1opu */ = new T(function(){
    return B(A1(_X0/* s1opt */,_WY/* Text.Read.Lex.lvl26 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_WX/* Text.Read.Lex.a63 */, function(_X2/* s1opv */){
    return E(_X1/* s1opu */);
  })));
},
_X3/* a65 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC2"));
}),
_X4/* lvl25 */ = 18,
_X5/* a66 */ = function(_X6/* s1opz */){
  var _X7/* s1opA */ = new T(function(){
    return B(A1(_X6/* s1opz */,_X4/* Text.Read.Lex.lvl25 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_X3/* Text.Read.Lex.a65 */, function(_X8/* s1opB */){
    return E(_X7/* s1opA */);
  })));
},
_X9/* a67 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC3"));
}),
_Xa/* lvl24 */ = 19,
_Xb/* a68 */ = function(_Xc/* s1opF */){
  var _Xd/* s1opG */ = new T(function(){
    return B(A1(_Xc/* s1opF */,_Xa/* Text.Read.Lex.lvl24 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_X9/* Text.Read.Lex.a67 */, function(_Xe/* s1opH */){
    return E(_Xd/* s1opG */);
  })));
},
_Xf/* a69 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DC4"));
}),
_Xg/* lvl23 */ = 20,
_Xh/* a70 */ = function(_Xi/* s1opL */){
  var _Xj/* s1opM */ = new T(function(){
    return B(A1(_Xi/* s1opL */,_Xg/* Text.Read.Lex.lvl23 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Xf/* Text.Read.Lex.a69 */, function(_Xk/* s1opN */){
    return E(_Xj/* s1opM */);
  })));
},
_Xl/* a71 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("NAK"));
}),
_Xm/* lvl22 */ = 21,
_Xn/* a72 */ = function(_Xo/* s1opR */){
  var _Xp/* s1opS */ = new T(function(){
    return B(A1(_Xo/* s1opR */,_Xm/* Text.Read.Lex.lvl22 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Xl/* Text.Read.Lex.a71 */, function(_Xq/* s1opT */){
    return E(_Xp/* s1opS */);
  })));
},
_Xr/* a73 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SYN"));
}),
_Xs/* lvl21 */ = 22,
_Xt/* a74 */ = function(_Xu/* s1opX */){
  var _Xv/* s1opY */ = new T(function(){
    return B(A1(_Xu/* s1opX */,_Xs/* Text.Read.Lex.lvl21 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Xr/* Text.Read.Lex.a73 */, function(_Xw/* s1opZ */){
    return E(_Xv/* s1opY */);
  })));
},
_Xx/* a75 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ETB"));
}),
_Xy/* lvl20 */ = 23,
_Xz/* a76 */ = function(_XA/* s1oq3 */){
  var _XB/* s1oq4 */ = new T(function(){
    return B(A1(_XA/* s1oq3 */,_Xy/* Text.Read.Lex.lvl20 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Xx/* Text.Read.Lex.a75 */, function(_XC/* s1oq5 */){
    return E(_XB/* s1oq4 */);
  })));
},
_XD/* a77 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("CAN"));
}),
_XE/* lvl19 */ = 24,
_XF/* a78 */ = function(_XG/* s1oq9 */){
  var _XH/* s1oqa */ = new T(function(){
    return B(A1(_XG/* s1oq9 */,_XE/* Text.Read.Lex.lvl19 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_XD/* Text.Read.Lex.a77 */, function(_XI/* s1oqb */){
    return E(_XH/* s1oqa */);
  })));
},
_XJ/* a79 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("EM"));
}),
_XK/* lvl18 */ = 25,
_XL/* a80 */ = function(_XM/* s1oqf */){
  var _XN/* s1oqg */ = new T(function(){
    return B(A1(_XM/* s1oqf */,_XK/* Text.Read.Lex.lvl18 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_XJ/* Text.Read.Lex.a79 */, function(_XO/* s1oqh */){
    return E(_XN/* s1oqg */);
  })));
},
_XP/* a81 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SUB"));
}),
_XQ/* lvl17 */ = 26,
_XR/* a82 */ = function(_XS/* s1oql */){
  var _XT/* s1oqm */ = new T(function(){
    return B(A1(_XS/* s1oql */,_XQ/* Text.Read.Lex.lvl17 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_XP/* Text.Read.Lex.a81 */, function(_XU/* s1oqn */){
    return E(_XT/* s1oqm */);
  })));
},
_XV/* a83 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("ESC"));
}),
_XW/* lvl16 */ = 27,
_XX/* a84 */ = function(_XY/* s1oqr */){
  var _XZ/* s1oqs */ = new T(function(){
    return B(A1(_XY/* s1oqr */,_XW/* Text.Read.Lex.lvl16 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_XV/* Text.Read.Lex.a83 */, function(_Y0/* s1oqt */){
    return E(_XZ/* s1oqs */);
  })));
},
_Y1/* a85 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("FS"));
}),
_Y2/* lvl15 */ = 28,
_Y3/* a86 */ = function(_Y4/* s1oqx */){
  var _Y5/* s1oqy */ = new T(function(){
    return B(A1(_Y4/* s1oqx */,_Y2/* Text.Read.Lex.lvl15 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Y1/* Text.Read.Lex.a85 */, function(_Y6/* s1oqz */){
    return E(_Y5/* s1oqy */);
  })));
},
_Y7/* a87 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GS"));
}),
_Y8/* lvl14 */ = 29,
_Y9/* a88 */ = function(_Ya/* s1oqD */){
  var _Yb/* s1oqE */ = new T(function(){
    return B(A1(_Ya/* s1oqD */,_Y8/* Text.Read.Lex.lvl14 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Y7/* Text.Read.Lex.a87 */, function(_Yc/* s1oqF */){
    return E(_Yb/* s1oqE */);
  })));
},
_Yd/* a89 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RS"));
}),
_Ye/* lvl13 */ = 30,
_Yf/* a90 */ = function(_Yg/* s1oqJ */){
  var _Yh/* s1oqK */ = new T(function(){
    return B(A1(_Yg/* s1oqJ */,_Ye/* Text.Read.Lex.lvl13 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Yd/* Text.Read.Lex.a89 */, function(_Yi/* s1oqL */){
    return E(_Yh/* s1oqK */);
  })));
},
_Yj/* a91 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("US"));
}),
_Yk/* lvl12 */ = 31,
_Yl/* a92 */ = function(_Ym/* s1oqP */){
  var _Yn/* s1oqQ */ = new T(function(){
    return B(A1(_Ym/* s1oqP */,_Yk/* Text.Read.Lex.lvl12 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Yj/* Text.Read.Lex.a91 */, function(_Yo/* s1oqR */){
    return E(_Yn/* s1oqQ */);
  })));
},
_Yp/* a93 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("SP"));
}),
_Yq/* x */ = 32,
_Yr/* a94 */ = function(_Ys/* s1oqV */){
  var _Yt/* s1oqW */ = new T(function(){
    return B(A1(_Ys/* s1oqV */,_Yq/* Text.Read.Lex.x */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Yp/* Text.Read.Lex.a93 */, function(_Yu/* s1oqX */){
    return E(_Yt/* s1oqW */);
  })));
},
_Yv/* a95 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("DEL"));
}),
_Yw/* x1 */ = 127,
_Yx/* a96 */ = function(_Yy/* s1or1 */){
  var _Yz/* s1or2 */ = new T(function(){
    return B(A1(_Yy/* s1or1 */,_Yw/* Text.Read.Lex.x1 */));
  });
  return new T1(1,B(_V5/* Text.ParserCombinators.ReadP.$wa6 */(_Yv/* Text.Read.Lex.a95 */, function(_YA/* s1or3 */){
    return E(_Yz/* s1or2 */);
  })));
},
_YB/* lvl47 */ = new T2(1,_Yx/* Text.Read.Lex.a96 */,_I/* GHC.Types.[] */),
_YC/* lvl48 */ = new T2(1,_Yr/* Text.Read.Lex.a94 */,_YB/* Text.Read.Lex.lvl47 */),
_YD/* lvl49 */ = new T2(1,_Yl/* Text.Read.Lex.a92 */,_YC/* Text.Read.Lex.lvl48 */),
_YE/* lvl50 */ = new T2(1,_Yf/* Text.Read.Lex.a90 */,_YD/* Text.Read.Lex.lvl49 */),
_YF/* lvl51 */ = new T2(1,_Y9/* Text.Read.Lex.a88 */,_YE/* Text.Read.Lex.lvl50 */),
_YG/* lvl52 */ = new T2(1,_Y3/* Text.Read.Lex.a86 */,_YF/* Text.Read.Lex.lvl51 */),
_YH/* lvl53 */ = new T2(1,_XX/* Text.Read.Lex.a84 */,_YG/* Text.Read.Lex.lvl52 */),
_YI/* lvl54 */ = new T2(1,_XR/* Text.Read.Lex.a82 */,_YH/* Text.Read.Lex.lvl53 */),
_YJ/* lvl55 */ = new T2(1,_XL/* Text.Read.Lex.a80 */,_YI/* Text.Read.Lex.lvl54 */),
_YK/* lvl56 */ = new T2(1,_XF/* Text.Read.Lex.a78 */,_YJ/* Text.Read.Lex.lvl55 */),
_YL/* lvl57 */ = new T2(1,_Xz/* Text.Read.Lex.a76 */,_YK/* Text.Read.Lex.lvl56 */),
_YM/* lvl58 */ = new T2(1,_Xt/* Text.Read.Lex.a74 */,_YL/* Text.Read.Lex.lvl57 */),
_YN/* lvl59 */ = new T2(1,_Xn/* Text.Read.Lex.a72 */,_YM/* Text.Read.Lex.lvl58 */),
_YO/* lvl60 */ = new T2(1,_Xh/* Text.Read.Lex.a70 */,_YN/* Text.Read.Lex.lvl59 */),
_YP/* lvl61 */ = new T2(1,_Xb/* Text.Read.Lex.a68 */,_YO/* Text.Read.Lex.lvl60 */),
_YQ/* lvl62 */ = new T2(1,_X5/* Text.Read.Lex.a66 */,_YP/* Text.Read.Lex.lvl61 */),
_YR/* lvl63 */ = new T2(1,_WZ/* Text.Read.Lex.a64 */,_YQ/* Text.Read.Lex.lvl62 */),
_YS/* lvl64 */ = new T2(1,_WT/* Text.Read.Lex.a62 */,_YR/* Text.Read.Lex.lvl63 */),
_YT/* lvl65 */ = new T2(1,_WN/* Text.Read.Lex.a60 */,_YS/* Text.Read.Lex.lvl64 */),
_YU/* lvl66 */ = new T2(1,_WH/* Text.Read.Lex.a58 */,_YT/* Text.Read.Lex.lvl65 */),
_YV/* lvl67 */ = new T2(1,_WB/* Text.Read.Lex.a56 */,_YU/* Text.Read.Lex.lvl66 */),
_YW/* lvl68 */ = new T2(1,_Wv/* Text.Read.Lex.a54 */,_YV/* Text.Read.Lex.lvl67 */),
_YX/* lvl69 */ = new T2(1,_Wp/* Text.Read.Lex.a52 */,_YW/* Text.Read.Lex.lvl68 */),
_YY/* lvl70 */ = new T2(1,_Wj/* Text.Read.Lex.a50 */,_YX/* Text.Read.Lex.lvl69 */),
_YZ/* lvl71 */ = new T2(1,_Wd/* Text.Read.Lex.a48 */,_YY/* Text.Read.Lex.lvl70 */),
_Z0/* lvl72 */ = new T2(1,_W7/* Text.Read.Lex.a46 */,_YZ/* Text.Read.Lex.lvl71 */),
_Z1/* lvl73 */ = new T2(1,_W1/* Text.Read.Lex.a44 */,_Z0/* Text.Read.Lex.lvl72 */),
_Z2/* lvl74 */ = new T2(1,_VV/* Text.Read.Lex.a42 */,_Z1/* Text.Read.Lex.lvl73 */),
_Z3/* lvl75 */ = new T2(1,_VP/* Text.Read.Lex.a40 */,_Z2/* Text.Read.Lex.lvl74 */),
_Z4/* lvl76 */ = new T2(1,_VJ/* Text.Read.Lex.a38 */,_Z3/* Text.Read.Lex.lvl75 */),
_Z5/* lvl77 */ = new T2(1,_VD/* Text.Read.Lex.a36 */,_Z4/* Text.Read.Lex.lvl76 */),
_Z6/* lvl78 */ = new T2(1,_Vx/* Text.Read.Lex.a34 */,_Z5/* Text.Read.Lex.lvl77 */),
_Z7/* lvl79 */ = new T2(1,_Vt/* Text.Read.Lex.a32 */,_Z6/* Text.Read.Lex.lvl78 */),
_Z8/* lexAscii */ = new T(function(){
  return B(_UX/* Text.ParserCombinators.ReadP.choice */(_Z7/* Text.Read.Lex.lvl79 */));
}),
_Z9/* lvl10 */ = 34,
_Za/* lvl11 */ = new T1(0,1114111),
_Zb/* lvl8 */ = 92,
_Zc/* lvl9 */ = 39,
_Zd/* lexChar2 */ = function(_Ze/* s1or7 */){
  var _Zf/* s1or8 */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_W6/* Text.Read.Lex.lvl7 */));
  }),
  _Zg/* s1or9 */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Wc/* Text.Read.Lex.lvl6 */));
  }),
  _Zh/* s1ora */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Wi/* Text.Read.Lex.lvl2 */));
  }),
  _Zi/* s1orb */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Wo/* Text.Read.Lex.lvl4 */));
  }),
  _Zj/* s1orc */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Wu/* Text.Read.Lex.lvl1 */));
  }),
  _Zk/* s1ord */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_WA/* Text.Read.Lex.lvl5 */));
  }),
  _Zl/* s1ore */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_WG/* Text.Read.Lex.lvl3 */));
  }),
  _Zm/* s1orf */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Zb/* Text.Read.Lex.lvl8 */));
  }),
  _Zn/* s1org */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Zc/* Text.Read.Lex.lvl9 */));
  }),
  _Zo/* s1orh */ = new T(function(){
    return B(A1(_Ze/* s1or7 */,_Z9/* Text.Read.Lex.lvl10 */));
  }),
  _Zp/* s1osl */ = new T(function(){
    var _Zq/* s1orE */ = function(_Zr/* s1oro */){
      var _Zs/* s1orp */ = new T(function(){
        return B(_Tf/* GHC.Integer.Type.smallInteger */(E(_Zr/* s1oro */)));
      }),
      _Zt/* s1orB */ = function(_Zu/* s1ors */){
        var _Zv/* s1ort */ = B(_TQ/* Text.Read.Lex.valInteger */(_Zs/* s1orp */, _Zu/* s1ors */));
        if(!B(_UN/* GHC.Integer.Type.leInteger */(_Zv/* s1ort */, _Za/* Text.Read.Lex.lvl11 */))){
          return new T0(2);
        }else{
          return new F(function(){return A1(_Ze/* s1or7 */,new T(function(){
            var _Zw/* s1orv */ = B(_UK/* GHC.Integer.Type.integerToInt */(_Zv/* s1ort */));
            if(_Zw/* s1orv */>>>0>1114111){
              return B(_UI/* GHC.Char.chr2 */(_Zw/* s1orv */));
            }else{
              return _Zw/* s1orv */;
            }
          }));});
        }
      };
      return new T1(1,B(_RR/* Text.Read.Lex.$wa6 */(_Zr/* s1oro */, _Zt/* s1orB */)));
    },
    _Zx/* s1osk */ = new T(function(){
      var _Zy/* s1orI */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Yk/* Text.Read.Lex.lvl12 */));
      }),
      _Zz/* s1orJ */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Ye/* Text.Read.Lex.lvl13 */));
      }),
      _ZA/* s1orK */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Y8/* Text.Read.Lex.lvl14 */));
      }),
      _ZB/* s1orL */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Y2/* Text.Read.Lex.lvl15 */));
      }),
      _ZC/* s1orM */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_XW/* Text.Read.Lex.lvl16 */));
      }),
      _ZD/* s1orN */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_XQ/* Text.Read.Lex.lvl17 */));
      }),
      _ZE/* s1orO */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_XK/* Text.Read.Lex.lvl18 */));
      }),
      _ZF/* s1orP */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_XE/* Text.Read.Lex.lvl19 */));
      }),
      _ZG/* s1orQ */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Xy/* Text.Read.Lex.lvl20 */));
      }),
      _ZH/* s1orR */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Xs/* Text.Read.Lex.lvl21 */));
      }),
      _ZI/* s1orS */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Xm/* Text.Read.Lex.lvl22 */));
      }),
      _ZJ/* s1orT */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Xg/* Text.Read.Lex.lvl23 */));
      }),
      _ZK/* s1orU */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Xa/* Text.Read.Lex.lvl24 */));
      }),
      _ZL/* s1orV */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_X4/* Text.Read.Lex.lvl25 */));
      }),
      _ZM/* s1orW */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_WY/* Text.Read.Lex.lvl26 */));
      }),
      _ZN/* s1orX */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_WS/* Text.Read.Lex.lvl27 */));
      }),
      _ZO/* s1orY */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_WM/* Text.Read.Lex.lvl28 */));
      }),
      _ZP/* s1orZ */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Vi/* Text.Read.Lex.lvl29 */));
      }),
      _ZQ/* s1os0 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_W0/* Text.Read.Lex.lvl30 */));
      }),
      _ZR/* s1os1 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_VU/* Text.Read.Lex.lvl31 */));
      }),
      _ZS/* s1os2 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_VO/* Text.Read.Lex.lvl32 */));
      }),
      _ZT/* s1os3 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_VI/* Text.Read.Lex.lvl33 */));
      }),
      _ZU/* s1os4 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_VC/* Text.Read.Lex.lvl34 */));
      }),
      _ZV/* s1os5 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Vo/* Text.Read.Lex.lvl35 */));
      }),
      _ZW/* s1os6 */ = new T(function(){
        return B(A1(_Ze/* s1or7 */,_Vw/* Text.Read.Lex.lvl36 */));
      }),
      _ZX/* s1os7 */ = function(_ZY/* s1os8 */){
        switch(E(_ZY/* s1os8 */)){
          case 64:
            return E(_ZW/* s1os6 */);
          case 65:
            return E(_ZV/* s1os5 */);
          case 66:
            return E(_ZU/* s1os4 */);
          case 67:
            return E(_ZT/* s1os3 */);
          case 68:
            return E(_ZS/* s1os2 */);
          case 69:
            return E(_ZR/* s1os1 */);
          case 70:
            return E(_ZQ/* s1os0 */);
          case 71:
            return E(_Zf/* s1or8 */);
          case 72:
            return E(_Zg/* s1or9 */);
          case 73:
            return E(_Zh/* s1ora */);
          case 74:
            return E(_Zi/* s1orb */);
          case 75:
            return E(_Zj/* s1orc */);
          case 76:
            return E(_Zk/* s1ord */);
          case 77:
            return E(_Zl/* s1ore */);
          case 78:
            return E(_ZP/* s1orZ */);
          case 79:
            return E(_ZO/* s1orY */);
          case 80:
            return E(_ZN/* s1orX */);
          case 81:
            return E(_ZM/* s1orW */);
          case 82:
            return E(_ZL/* s1orV */);
          case 83:
            return E(_ZK/* s1orU */);
          case 84:
            return E(_ZJ/* s1orT */);
          case 85:
            return E(_ZI/* s1orS */);
          case 86:
            return E(_ZH/* s1orR */);
          case 87:
            return E(_ZG/* s1orQ */);
          case 88:
            return E(_ZF/* s1orP */);
          case 89:
            return E(_ZE/* s1orO */);
          case 90:
            return E(_ZD/* s1orN */);
          case 91:
            return E(_ZC/* s1orM */);
          case 92:
            return E(_ZB/* s1orL */);
          case 93:
            return E(_ZA/* s1orK */);
          case 94:
            return E(_Zz/* s1orJ */);
          case 95:
            return E(_Zy/* s1orI */);
          default:
            return new T0(2);
        }
      };
      return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_ZZ/* s1osd */){
        return (E(_ZZ/* s1osd */)==94) ? E(new T1(0,_ZX/* s1os7 */)) : new T0(2);
      }), new T(function(){
        return B(A1(_Z8/* Text.Read.Lex.lexAscii */,_Ze/* s1or7 */));
      })));
    });
    return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_Ra/* Text.ParserCombinators.ReadP.$wa */(_UE/* Text.Read.Lex.a4 */, _UG/* Text.Read.Lex.a5 */, _Zq/* s1orE */))), _Zx/* s1osk */));
  });
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_100/* s1ori */){
    switch(E(_100/* s1ori */)){
      case 34:
        return E(_Zo/* s1orh */);
      case 39:
        return E(_Zn/* s1org */);
      case 92:
        return E(_Zm/* s1orf */);
      case 97:
        return E(_Zf/* s1or8 */);
      case 98:
        return E(_Zg/* s1or9 */);
      case 102:
        return E(_Zk/* s1ord */);
      case 110:
        return E(_Zi/* s1orb */);
      case 114:
        return E(_Zl/* s1ore */);
      case 116:
        return E(_Zh/* s1ora */);
      case 118:
        return E(_Zj/* s1orc */);
      default:
        return new T0(2);
    }
  }), _Zp/* s1osl */);});
},
_101/* a */ = function(_102/* s1iyn */){
  return new F(function(){return A1(_102/* s1iyn */,_0/* GHC.Tuple.() */);});
},
_103/* skipSpaces_skip */ = function(_104/* s1iIB */){
  var _105/* s1iIC */ = E(_104/* s1iIB */);
  if(!_105/* s1iIC */._){
    return E(_101/* Text.ParserCombinators.ReadP.a */);
  }else{
    var _106/* s1iIF */ = E(_105/* s1iIC */.a),
    _107/* s1iIH */ = _106/* s1iIF */>>>0,
    _108/* s1iIJ */ = new T(function(){
      return B(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */(_105/* s1iIC */.b));
    });
    if(_107/* s1iIH */>887){
      var _109/* s1iIO */ = u_iswspace/* EXTERNAL */(_106/* s1iIF */);
      if(!E(_109/* s1iIO */)){
        return E(_101/* Text.ParserCombinators.ReadP.a */);
      }else{
        var _10a/* s1iIW */ = function(_10b/* s1iIS */){
          var _10c/* s1iIT */ = new T(function(){
            return B(A1(_108/* s1iIJ */,_10b/* s1iIS */));
          });
          return new T1(0,function(_10d/* s1iIU */){
            return E(_10c/* s1iIT */);
          });
        };
        return E(_10a/* s1iIW */);
      }
    }else{
      var _10e/* s1iIX */ = E(_107/* s1iIH */);
      if(_10e/* s1iIX */==32){
        var _10f/* s1iJg */ = function(_10g/* s1iJc */){
          var _10h/* s1iJd */ = new T(function(){
            return B(A1(_108/* s1iIJ */,_10g/* s1iJc */));
          });
          return new T1(0,function(_10i/* s1iJe */){
            return E(_10h/* s1iJd */);
          });
        };
        return E(_10f/* s1iJg */);
      }else{
        if(_10e/* s1iIX */-9>>>0>4){
          if(E(_10e/* s1iIX */)==160){
            var _10j/* s1iJ6 */ = function(_10k/* s1iJ2 */){
              var _10l/* s1iJ3 */ = new T(function(){
                return B(A1(_108/* s1iIJ */,_10k/* s1iJ2 */));
              });
              return new T1(0,function(_10m/* s1iJ4 */){
                return E(_10l/* s1iJ3 */);
              });
            };
            return E(_10j/* s1iJ6 */);
          }else{
            return E(_101/* Text.ParserCombinators.ReadP.a */);
          }
        }else{
          var _10n/* s1iJb */ = function(_10o/* s1iJ7 */){
            var _10p/* s1iJ8 */ = new T(function(){
              return B(A1(_108/* s1iIJ */,_10o/* s1iJ7 */));
            });
            return new T1(0,function(_10q/* s1iJ9 */){
              return E(_10p/* s1iJ8 */);
            });
          };
          return E(_10n/* s1iJb */);
        }
      }
    }
  }
},
_10r/* a97 */ = function(_10s/* s1osm */){
  var _10t/* s1osn */ = new T(function(){
    return B(_10r/* Text.Read.Lex.a97 */(_10s/* s1osm */));
  }),
  _10u/* s1oso */ = function(_10v/* s1osp */){
    return (E(_10v/* s1osp */)==92) ? E(_10t/* s1osn */) : new T0(2);
  },
  _10w/* s1osu */ = function(_10x/* s1osv */){
    return E(new T1(0,_10u/* s1oso */));
  },
  _10y/* s1osy */ = new T1(1,function(_10z/* s1osx */){
    return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_10z/* s1osx */, _10w/* s1osu */);});
  }),
  _10A/* s1osz */ = new T(function(){
    return B(_Zd/* Text.Read.Lex.lexChar2 */(function(_10B/* s1osA */){
      return new F(function(){return A1(_10s/* s1osm */,new T2(0,_10B/* s1osA */,_aC/* GHC.Types.True */));});
    }));
  }),
  _10C/* s1osD */ = function(_10D/* s1osE */){
    var _10E/* s1osH */ = E(_10D/* s1osE */);
    if(_10E/* s1osH */==38){
      return E(_10t/* s1osn */);
    }else{
      var _10F/* s1osI */ = _10E/* s1osH */>>>0;
      if(_10F/* s1osI */>887){
        var _10G/* s1osO */ = u_iswspace/* EXTERNAL */(_10E/* s1osH */);
        return (E(_10G/* s1osO */)==0) ? new T0(2) : E(_10y/* s1osy */);
      }else{
        var _10H/* s1osS */ = E(_10F/* s1osI */);
        return (_10H/* s1osS */==32) ? E(_10y/* s1osy */) : (_10H/* s1osS */-9>>>0>4) ? (E(_10H/* s1osS */)==160) ? E(_10y/* s1osy */) : new T0(2) : E(_10y/* s1osy */);
      }
    }
  };
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_10I/* s1osY */){
    return (E(_10I/* s1osY */)==92) ? E(new T1(0,_10C/* s1osD */)) : new T0(2);
  }), new T1(0,function(_10J/* s1ot4 */){
    var _10K/* s1ot5 */ = E(_10J/* s1ot4 */);
    if(E(_10K/* s1ot5 */)==92){
      return E(_10A/* s1osz */);
    }else{
      return new F(function(){return A1(_10s/* s1osm */,new T2(0,_10K/* s1ot5 */,_2G/* GHC.Types.False */));});
    }
  }));});
},
_10L/* a98 */ = function(_10M/* s1otb */, _10N/* s1otc */){
  var _10O/* s1otd */ = new T(function(){
    return B(A1(_10N/* s1otc */,new T1(1,new T(function(){
      return B(A1(_10M/* s1otb */,_I/* GHC.Types.[] */));
    }))));
  }),
  _10P/* s1otu */ = function(_10Q/* s1otg */){
    var _10R/* s1oth */ = E(_10Q/* s1otg */),
    _10S/* s1otk */ = E(_10R/* s1oth */.a);
    if(E(_10S/* s1otk */)==34){
      if(!E(_10R/* s1oth */.b)){
        return E(_10O/* s1otd */);
      }else{
        return new F(function(){return _10L/* Text.Read.Lex.a98 */(function(_10T/* s1otr */){
          return new F(function(){return A1(_10M/* s1otb */,new T2(1,_10S/* s1otk */,_10T/* s1otr */));});
        }, _10N/* s1otc */);});
      }
    }else{
      return new F(function(){return _10L/* Text.Read.Lex.a98 */(function(_10U/* s1otn */){
        return new F(function(){return A1(_10M/* s1otb */,new T2(1,_10S/* s1otk */,_10U/* s1otn */));});
      }, _10N/* s1otc */);});
    }
  };
  return new F(function(){return _10r/* Text.Read.Lex.a97 */(_10P/* s1otu */);});
},
_10V/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_\'"));
}),
_10W/* $wisIdfChar */ = function(_10X/* s1otE */){
  var _10Y/* s1otH */ = u_iswalnum/* EXTERNAL */(_10X/* s1otE */);
  if(!E(_10Y/* s1otH */)){
    return new F(function(){return _Ur/* GHC.List.elem */(_QG/* GHC.Classes.$fEqChar */, _10X/* s1otE */, _10V/* Text.Read.Lex.lvl45 */);});
  }else{
    return true;
  }
},
_10Z/* isIdfChar */ = function(_110/* s1otM */){
  return new F(function(){return _10W/* Text.Read.Lex.$wisIdfChar */(E(_110/* s1otM */));});
},
_111/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(",;()[]{}`"));
}),
_112/* a7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("=>"));
}),
_113/* a8 */ = new T2(1,_112/* Text.Read.Lex.a7 */,_I/* GHC.Types.[] */),
_114/* a9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("~"));
}),
_115/* a10 */ = new T2(1,_114/* Text.Read.Lex.a9 */,_113/* Text.Read.Lex.a8 */),
_116/* a11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("@"));
}),
_117/* a12 */ = new T2(1,_116/* Text.Read.Lex.a11 */,_115/* Text.Read.Lex.a10 */),
_118/* a13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("->"));
}),
_119/* a14 */ = new T2(1,_118/* Text.Read.Lex.a13 */,_117/* Text.Read.Lex.a12 */),
_11a/* a15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<-"));
}),
_11b/* a16 */ = new T2(1,_11a/* Text.Read.Lex.a15 */,_119/* Text.Read.Lex.a14 */),
_11c/* a17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("|"));
}),
_11d/* a18 */ = new T2(1,_11c/* Text.Read.Lex.a17 */,_11b/* Text.Read.Lex.a16 */),
_11e/* a19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\\"));
}),
_11f/* a20 */ = new T2(1,_11e/* Text.Read.Lex.a19 */,_11d/* Text.Read.Lex.a18 */),
_11g/* a21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("="));
}),
_11h/* a22 */ = new T2(1,_11g/* Text.Read.Lex.a21 */,_11f/* Text.Read.Lex.a20 */),
_11i/* a23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("::"));
}),
_11j/* a24 */ = new T2(1,_11i/* Text.Read.Lex.a23 */,_11h/* Text.Read.Lex.a22 */),
_11k/* a25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".."));
}),
_11l/* reserved_ops */ = new T2(1,_11k/* Text.Read.Lex.a25 */,_11j/* Text.Read.Lex.a24 */),
_11m/* expect2 */ = function(_11n/* s1otP */){
  var _11o/* s1otQ */ = new T(function(){
    return B(A1(_11n/* s1otP */,_RO/* Text.Read.Lex.EOF */));
  }),
  _11p/* s1ovk */ = new T(function(){
    var _11q/* s1otX */ = new T(function(){
      var _11r/* s1ou6 */ = function(_11s/* s1otY */){
        var _11t/* s1otZ */ = new T(function(){
          return B(A1(_11n/* s1otP */,new T1(0,_11s/* s1otY */)));
        });
        return new T1(0,function(_11u/* s1ou1 */){
          return (E(_11u/* s1ou1 */)==39) ? E(_11t/* s1otZ */) : new T0(2);
        });
      };
      return B(_Zd/* Text.Read.Lex.lexChar2 */(_11r/* s1ou6 */));
    }),
    _11v/* s1ou7 */ = function(_11w/* s1ou8 */){
      var _11x/* s1ou9 */ = E(_11w/* s1ou8 */);
      switch(E(_11x/* s1ou9 */)){
        case 39:
          return new T0(2);
        case 92:
          return E(_11q/* s1otX */);
        default:
          var _11y/* s1ouc */ = new T(function(){
            return B(A1(_11n/* s1otP */,new T1(0,_11x/* s1ou9 */)));
          });
          return new T1(0,function(_11z/* s1oue */){
            return (E(_11z/* s1oue */)==39) ? E(_11y/* s1ouc */) : new T0(2);
          });
      }
    },
    _11A/* s1ovj */ = new T(function(){
      var _11B/* s1ouq */ = new T(function(){
        return B(_10L/* Text.Read.Lex.a98 */(_4/* GHC.Base.id */, _11n/* s1otP */));
      }),
      _11C/* s1ovi */ = new T(function(){
        var _11D/* s1ovh */ = new T(function(){
          var _11E/* s1ovg */ = new T(function(){
            var _11F/* s1ovb */ = function(_11G/* s1ouP */){
              var _11H/* s1ouQ */ = E(_11G/* s1ouP */),
              _11I/* s1ouU */ = u_iswalpha/* EXTERNAL */(_11H/* s1ouQ */);
              return (E(_11I/* s1ouU */)==0) ? (E(_11H/* s1ouQ */)==95) ? new T1(1,B(_RA/* Text.ParserCombinators.ReadP.$wa3 */(_10Z/* Text.Read.Lex.isIdfChar */, function(_11J/* s1ov5 */){
                return new F(function(){return A1(_11n/* s1otP */,new T1(3,new T2(1,_11H/* s1ouQ */,_11J/* s1ov5 */)));});
              }))) : new T0(2) : new T1(1,B(_RA/* Text.ParserCombinators.ReadP.$wa3 */(_10Z/* Text.Read.Lex.isIdfChar */, function(_11K/* s1ouY */){
                return new F(function(){return A1(_11n/* s1otP */,new T1(3,new T2(1,_11H/* s1ouQ */,_11K/* s1ouY */)));});
              })));
            };
            return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_11F/* s1ovb */), new T(function(){
              return new T1(1,B(_Ra/* Text.ParserCombinators.ReadP.$wa */(_SM/* Text.Read.Lex.a2 */, _Un/* Text.Read.Lex.a27 */, _11n/* s1otP */)));
            })));
          }),
          _11L/* s1ouN */ = function(_11M/* s1ouD */){
            return (!B(_Ur/* GHC.List.elem */(_QG/* GHC.Classes.$fEqChar */, _11M/* s1ouD */, _Uw/* Text.Read.Lex.lvl44 */))) ? new T0(2) : new T1(1,B(_RA/* Text.ParserCombinators.ReadP.$wa3 */(_Ux/* Text.Read.Lex.a6 */, function(_11N/* s1ouF */){
              var _11O/* s1ouG */ = new T2(1,_11M/* s1ouD */,_11N/* s1ouF */);
              if(!B(_Ur/* GHC.List.elem */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, _11O/* s1ouG */, _11l/* Text.Read.Lex.reserved_ops */))){
                return new F(function(){return A1(_11n/* s1otP */,new T1(4,_11O/* s1ouG */));});
              }else{
                return new F(function(){return A1(_11n/* s1otP */,new T1(2,_11O/* s1ouG */));});
              }
            })));
          };
          return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,_11L/* s1ouN */), _11E/* s1ovg */));
        });
        return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11P/* s1oux */){
          if(!B(_Ur/* GHC.List.elem */(_QG/* GHC.Classes.$fEqChar */, _11P/* s1oux */, _111/* Text.Read.Lex.lvl43 */))){
            return new T0(2);
          }else{
            return new F(function(){return A1(_11n/* s1otP */,new T1(2,new T2(1,_11P/* s1oux */,_I/* GHC.Types.[] */)));});
          }
        }), _11D/* s1ovh */));
      });
      return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11Q/* s1our */){
        return (E(_11Q/* s1our */)==34) ? E(_11B/* s1ouq */) : new T0(2);
      }), _11C/* s1ovi */));
    });
    return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(0,function(_11R/* s1ouk */){
      return (E(_11R/* s1ouk */)==39) ? E(new T1(0,_11v/* s1ou7 */)) : new T0(2);
    }), _11A/* s1ovj */));
  });
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_11S/* s1otR */){
    return (E(_11S/* s1otR */)._==0) ? E(_11o/* s1otQ */) : new T0(2);
  }), _11p/* s1ovk */);});
},
_11T/* minPrec */ = 0,
_11U/* $wa3 */ = function(_11V/* s1viS */, _11W/* s1viT */){
  var _11X/* s1viU */ = new T(function(){
    var _11Y/* s1viV */ = new T(function(){
      var _11Z/* s1vj8 */ = function(_120/* s1viW */){
        var _121/* s1viX */ = new T(function(){
          var _122/* s1viY */ = new T(function(){
            return B(A1(_11W/* s1viT */,_120/* s1viW */));
          });
          return B(_11m/* Text.Read.Lex.expect2 */(function(_123/* s1viZ */){
            var _124/* s1vj0 */ = E(_123/* s1viZ */);
            return (_124/* s1vj0 */._==2) ? (!B(_Lg/* GHC.Base.eqString */(_124/* s1vj0 */.a, _Qz/* GHC.Read.$fRead(,)4 */))) ? new T0(2) : E(_122/* s1viY */) : new T0(2);
          }));
        }),
        _125/* s1vj4 */ = function(_126/* s1vj5 */){
          return E(_121/* s1viX */);
        };
        return new T1(1,function(_127/* s1vj6 */){
          return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_127/* s1vj6 */, _125/* s1vj4 */);});
        });
      };
      return B(A2(_11V/* s1viS */,_11T/* Text.ParserCombinators.ReadPrec.minPrec */, _11Z/* s1vj8 */));
    });
    return B(_11m/* Text.Read.Lex.expect2 */(function(_128/* s1vj9 */){
      var _129/* s1vja */ = E(_128/* s1vj9 */);
      return (_129/* s1vja */._==2) ? (!B(_Lg/* GHC.Base.eqString */(_129/* s1vja */.a, _Qy/* GHC.Read.$fRead(,)3 */))) ? new T0(2) : E(_11Y/* s1viV */) : new T0(2);
    }));
  }),
  _12a/* s1vje */ = function(_12b/* s1vjf */){
    return E(_11X/* s1viU */);
  };
  return function(_12c/* s1vjg */){
    return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12c/* s1vjg */, _12a/* s1vje */);});
  };
},
_12d/* $fReadDouble10 */ = function(_12e/* s1vjn */, _12f/* s1vjo */){
  var _12g/* s1vjp */ = function(_12h/* s1vjq */){
    var _12i/* s1vjr */ = new T(function(){
      return B(A1(_12e/* s1vjn */,_12h/* s1vjq */));
    }),
    _12j/* s1vjx */ = function(_12k/* s1vjs */){
      return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_12i/* s1vjr */,_12k/* s1vjs */)), new T(function(){
        return new T1(1,B(_11U/* GHC.Read.$wa3 */(_12g/* s1vjp */, _12k/* s1vjs */)));
      }));});
    };
    return E(_12j/* s1vjx */);
  },
  _12l/* s1vjy */ = new T(function(){
    return B(A1(_12e/* s1vjn */,_12f/* s1vjo */));
  }),
  _12m/* s1vjE */ = function(_12n/* s1vjz */){
    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(A1(_12l/* s1vjy */,_12n/* s1vjz */)), new T(function(){
      return new T1(1,B(_11U/* GHC.Read.$wa3 */(_12g/* s1vjp */, _12n/* s1vjz */)));
    }));});
  };
  return E(_12m/* s1vjE */);
},
_12o/* $fReadInt3 */ = function(_12p/* s1vlT */, _12q/* s1vlU */){
  var _12r/* s1vmt */ = function(_12s/* s1vlV */, _12t/* s1vlW */){
    var _12u/* s1vlX */ = function(_12v/* s1vlY */){
      return new F(function(){return A1(_12t/* s1vlW */,new T(function(){
        return  -E(_12v/* s1vlY */);
      }));});
    },
    _12w/* s1vm5 */ = new T(function(){
      return B(_11m/* Text.Read.Lex.expect2 */(function(_12x/* s1vm4 */){
        return new F(function(){return A3(_12p/* s1vlT */,_12x/* s1vm4 */, _12s/* s1vlV */, _12u/* s1vlX */);});
      }));
    }),
    _12y/* s1vm6 */ = function(_12z/* s1vm7 */){
      return E(_12w/* s1vm5 */);
    },
    _12A/* s1vm8 */ = function(_12B/* s1vm9 */){
      return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12B/* s1vm9 */, _12y/* s1vm6 */);});
    },
    _12C/* s1vmo */ = new T(function(){
      return B(_11m/* Text.Read.Lex.expect2 */(function(_12D/* s1vmc */){
        var _12E/* s1vmd */ = E(_12D/* s1vmc */);
        if(_12E/* s1vmd */._==4){
          var _12F/* s1vmf */ = E(_12E/* s1vmd */.a);
          if(!_12F/* s1vmf */._){
            return new F(function(){return A3(_12p/* s1vlT */,_12E/* s1vmd */, _12s/* s1vlV */, _12t/* s1vlW */);});
          }else{
            if(E(_12F/* s1vmf */.a)==45){
              if(!E(_12F/* s1vmf */.b)._){
                return E(new T1(1,_12A/* s1vm8 */));
              }else{
                return new F(function(){return A3(_12p/* s1vlT */,_12E/* s1vmd */, _12s/* s1vlV */, _12t/* s1vlW */);});
              }
            }else{
              return new F(function(){return A3(_12p/* s1vlT */,_12E/* s1vmd */, _12s/* s1vlV */, _12t/* s1vlW */);});
            }
          }
        }else{
          return new F(function(){return A3(_12p/* s1vlT */,_12E/* s1vmd */, _12s/* s1vlV */, _12t/* s1vlW */);});
        }
      }));
    }),
    _12G/* s1vmp */ = function(_12H/* s1vmq */){
      return E(_12C/* s1vmo */);
    };
    return new T1(1,function(_12I/* s1vmr */){
      return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_12I/* s1vmr */, _12G/* s1vmp */);});
    });
  };
  return new F(function(){return _12d/* GHC.Read.$fReadDouble10 */(_12r/* s1vmt */, _12q/* s1vlU */);});
},
_12J/* numberToInteger */ = function(_12K/* s1ojv */){
  var _12L/* s1ojw */ = E(_12K/* s1ojv */);
  if(!_12L/* s1ojw */._){
    var _12M/* s1ojy */ = _12L/* s1ojw */.b,
    _12N/* s1ojF */ = new T(function(){
      return B(_Tz/* Text.Read.Lex.numberToFixed_go */(new T(function(){
        return B(_Tf/* GHC.Integer.Type.smallInteger */(E(_12L/* s1ojw */.a)));
      }), new T(function(){
        return B(_Ta/* GHC.List.$wlenAcc */(_12M/* s1ojy */, 0));
      },1), B(_2S/* GHC.Base.map */(_Th/* Text.Read.Lex.numberToFixed2 */, _12M/* s1ojy */))));
    });
    return new T1(1,_12N/* s1ojF */);
  }else{
    return (E(_12L/* s1ojw */.b)._==0) ? (E(_12L/* s1ojw */.c)._==0) ? new T1(1,new T(function(){
      return B(_TQ/* Text.Read.Lex.valInteger */(_T9/* Text.Read.Lex.numberToFixed1 */, _12L/* s1ojw */.a));
    })) : __Z/* EXTERNAL */ : __Z/* EXTERNAL */;
  }
},
_12O/* pfail1 */ = function(_12P/* s1kH8 */, _12Q/* s1kH9 */){
  return new T0(2);
},
_12R/* $fReadInt_$sconvertInt */ = function(_12S/* s1vie */){
  var _12T/* s1vif */ = E(_12S/* s1vie */);
  if(_12T/* s1vif */._==5){
    var _12U/* s1vih */ = B(_12J/* Text.Read.Lex.numberToInteger */(_12T/* s1vif */.a));
    if(!_12U/* s1vih */._){
      return E(_12O/* Text.ParserCombinators.ReadPrec.pfail1 */);
    }else{
      var _12V/* s1vij */ = new T(function(){
        return B(_UK/* GHC.Integer.Type.integerToInt */(_12U/* s1vih */.a));
      });
      return function(_12W/* s1vil */, _12X/* s1vim */){
        return new F(function(){return A1(_12X/* s1vim */,_12V/* s1vij */);});
      };
    }
  }else{
    return E(_12O/* Text.ParserCombinators.ReadPrec.pfail1 */);
  }
},
_12Y/* readEither5 */ = function(_12Z/* s2Rfe */){
  var _130/* s2Rfg */ = function(_131/* s2Rfh */){
    return E(new T2(3,_12Z/* s2Rfe */,_R1/* Text.ParserCombinators.ReadP.Fail */));
  };
  return new T1(1,function(_132/* s2Rfi */){
    return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_132/* s2Rfi */, _130/* s2Rfg */);});
  });
},
_133/* updateElementValue1 */ = new T(function(){
  return B(A3(_12o/* GHC.Read.$fReadInt3 */,_12R/* GHC.Read.$fReadInt_$sconvertInt */, _11T/* Text.ParserCombinators.ReadPrec.minPrec */, _12Y/* Text.Read.readEither5 */));
}),
_134/* updateElementValue */ = function(_135/* so2A */, _136/* so2B */){
  var _137/* so2C */ = E(_135/* so2A */);
  switch(_137/* so2C */._){
    case 1:
      return new T3(1,_137/* so2C */.a,_136/* so2B */,_137/* so2C */.c);
    case 2:
      return new T3(2,_137/* so2C */.a,_136/* so2B */,_137/* so2C */.c);
    case 3:
      return new T3(3,_137/* so2C */.a,_136/* so2B */,_137/* so2C */.c);
    case 4:
      return new T4(4,_137/* so2C */.a,new T(function(){
        var _138/* so2R */ = B(_OF/* Text.Read.readEither6 */(B(_OM/* Text.ParserCombinators.ReadP.run */(_133/* FormEngine.FormElement.Updating.updateElementValue1 */, _136/* so2B */))));
        if(!_138/* so2R */._){
          return __Z/* EXTERNAL */;
        }else{
          if(!E(_138/* so2R */.b)._){
            return new T1(1,_138/* so2R */.a);
          }else{
            return __Z/* EXTERNAL */;
          }
        }
      }),_137/* so2C */.c,_137/* so2C */.d);
    case 6:
      var _139/* so3n */ = new T(function(){
        return B(_2S/* GHC.Base.map */(function(_13a/* so31 */){
          var _13b/* so32 */ = E(_13a/* so31 */);
          if(!_13b/* so32 */._){
            var _13c/* so35 */ = E(_13b/* so32 */.a);
            return (_13c/* so35 */._==0) ? (!B(_Lg/* GHC.Base.eqString */(_13c/* so35 */.a, _136/* so2B */))) ? new T2(0,_13c/* so35 */,_2G/* GHC.Types.False */) : new T2(0,_13c/* so35 */,_aC/* GHC.Types.True */) : (!B(_Lg/* GHC.Base.eqString */(_13c/* so35 */.b, _136/* so2B */))) ? new T2(0,_13c/* so35 */,_2G/* GHC.Types.False */) : new T2(0,_13c/* so35 */,_aC/* GHC.Types.True */);
          }else{
            var _13d/* so3e */ = _13b/* so32 */.c,
            _13e/* so3f */ = E(_13b/* so32 */.a);
            return (_13e/* so3f */._==0) ? (!B(_Lg/* GHC.Base.eqString */(_13e/* so3f */.a, _136/* so2B */))) ? new T3(1,_13e/* so3f */,_2G/* GHC.Types.False */,_13d/* so3e */) : new T3(1,_13e/* so3f */,_aC/* GHC.Types.True */,_13d/* so3e */) : (!B(_Lg/* GHC.Base.eqString */(_13e/* so3f */.b, _136/* so2B */))) ? new T3(1,_13e/* so3f */,_2G/* GHC.Types.False */,_13d/* so3e */) : new T3(1,_13e/* so3f */,_aC/* GHC.Types.True */,_13d/* so3e */);
          }
        }, _137/* so2C */.b));
      });
      return new T3(6,_137/* so2C */.a,_139/* so3n */,_137/* so2C */.c);
    case 7:
      return new T3(7,_137/* so2C */.a,new T(function(){
        if(!B(_Lg/* GHC.Base.eqString */(_136/* so2B */, _I/* GHC.Types.[] */))){
          return new T1(1,_136/* so2B */);
        }else{
          return __Z/* EXTERNAL */;
        }
      }),_137/* so2C */.c);
    default:
      return E(_137/* so2C */);
  }
},
_13f/* identity2elementUpdated2 */ = function(_13g/* so3t */, _/* EXTERNAL */){
  var _13h/* so3v */ = E(_13g/* so3t */);
  switch(_13h/* so3v */._){
    case 0:
      var _13i/* so3K */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13j/* so3S */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13i/* so3K */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13k/* so3W */ = String/* EXTERNAL */(_13j/* so3S */);
          return fromJSStr/* EXTERNAL */(_13k/* so3W */);
        })));
      });
    case 1:
      var _13l/* so4i */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13m/* so4q */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13l/* so4i */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13n/* so4u */ = String/* EXTERNAL */(_13m/* so4q */);
          return fromJSStr/* EXTERNAL */(_13n/* so4u */);
        })));
      });
    case 2:
      var _13o/* so4Q */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13p/* so4Y */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13o/* so4Q */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13q/* so52 */ = String/* EXTERNAL */(_13p/* so4Y */);
          return fromJSStr/* EXTERNAL */(_13q/* so52 */);
        })));
      });
    case 3:
      var _13r/* so5o */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13s/* so5w */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13r/* so5o */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13t/* so5A */ = String/* EXTERNAL */(_13s/* so5w */);
          return fromJSStr/* EXTERNAL */(_13t/* so5A */);
        })));
      });
    case 4:
      var _13u/* so5I */ = _13h/* so3v */.a,
      _13v/* so5L */ = _13h/* so3v */.d,
      _13w/* so5O */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_13u/* so5I */)).b,
      _13x/* so5X */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(_13w/* so5O */)), _/* EXTERNAL */)),
      _13y/* so65 */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13x/* so5X */)),
      _13z/* so6a */ = B(_Ox/* FormEngine.JQuery.getRadioValue1 */(new T(function(){
        return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(_13w/* so5O */)), _OE/* FormEngine.FormItem.nfiUnitId1 */));
      },1), _/* EXTERNAL */));
      return new T(function(){
        var _13A/* so6d */ = new T(function(){
          var _13B/* so6f */ = String/* EXTERNAL */(_13y/* so65 */);
          return fromJSStr/* EXTERNAL */(_13B/* so6f */);
        }),
        _13C/* so6l */ = function(_13D/* so6m */){
          return new T4(4,_13u/* so5I */,new T(function(){
            var _13E/* so6o */ = B(_OF/* Text.Read.readEither6 */(B(_OM/* Text.ParserCombinators.ReadP.run */(_133/* FormEngine.FormElement.Updating.updateElementValue1 */, _13A/* so6d */))));
            if(!_13E/* so6o */._){
              return __Z/* EXTERNAL */;
            }else{
              if(!E(_13E/* so6o */.b)._){
                return new T1(1,_13E/* so6o */.a);
              }else{
                return __Z/* EXTERNAL */;
              }
            }
          }),_2o/* GHC.Base.Nothing */,_13v/* so5L */);
        };
        if(!B(_Lg/* GHC.Base.eqString */(_13z/* so6a */, _OD/* FormEngine.FormElement.Updating.lvl2 */))){
          var _13F/* so6w */ = E(_13z/* so6a */);
          if(!_13F/* so6w */._){
            return B(_13C/* so6l */(_/* EXTERNAL */));
          }else{
            return new T4(4,_13u/* so5I */,new T(function(){
              var _13G/* so6A */ = B(_OF/* Text.Read.readEither6 */(B(_OM/* Text.ParserCombinators.ReadP.run */(_133/* FormEngine.FormElement.Updating.updateElementValue1 */, _13A/* so6d */))));
              if(!_13G/* so6A */._){
                return __Z/* EXTERNAL */;
              }else{
                if(!E(_13G/* so6A */.b)._){
                  return new T1(1,_13G/* so6A */.a);
                }else{
                  return __Z/* EXTERNAL */;
                }
              }
            }),new T1(1,_13F/* so6w */),_13v/* so5L */);
          }
        }else{
          return B(_13C/* so6l */(_/* EXTERNAL */));
        }
      });
    case 5:
      var _13H/* so6W */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13I/* so74 */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13H/* so6W */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13J/* so78 */ = String/* EXTERNAL */(_13I/* so74 */);
          return fromJSStr/* EXTERNAL */(_13J/* so78 */);
        })));
      });
    case 6:
      var _13K/* so7u */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13L/* so7C */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13K/* so7u */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13M/* so7G */ = String/* EXTERNAL */(_13L/* so7C */);
          return fromJSStr/* EXTERNAL */(_13M/* so7G */);
        })));
      });
    case 7:
      var _13N/* so82 */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13O/* so8a */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13N/* so82 */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13P/* so8e */ = String/* EXTERNAL */(_13O/* so8a */);
          return fromJSStr/* EXTERNAL */(_13P/* so8e */);
        })));
      });
    case 8:
      var _13Q/* so8A */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13R/* so8I */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13Q/* so8A */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13S/* so8M */ = String/* EXTERNAL */(_13R/* so8I */);
          return fromJSStr/* EXTERNAL */(_13S/* so8M */);
        })));
      });
    case 9:
      var _13T/* so99 */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13U/* so9h */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13T/* so99 */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13V/* so9l */ = String/* EXTERNAL */(_13U/* so9h */);
          return fromJSStr/* EXTERNAL */(_13V/* so9l */);
        })));
      });
    case 10:
      var _13W/* so9H */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _13X/* so9P */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13W/* so9H */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _13Y/* so9T */ = String/* EXTERNAL */(_13X/* so9P */);
          return fromJSStr/* EXTERNAL */(_13Y/* so9T */);
        })));
      });
    case 11:
      var _13Z/* soae */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _140/* soam */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_13Z/* soae */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _141/* soaq */ = String/* EXTERNAL */(_140/* soam */);
          return fromJSStr/* EXTERNAL */(_141/* soaq */);
        })));
      });
    default:
      var _142/* soaL */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_13h/* so3v */.a)).b)), _/* EXTERNAL */)),
      _143/* soaT */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_142/* soaL */));
      return new T(function(){
        return B(_134/* FormEngine.FormElement.Updating.updateElementValue */(_13h/* so3v */, new T(function(){
          var _144/* soaX */ = String/* EXTERNAL */(_143/* soaT */);
          return fromJSStr/* EXTERNAL */(_144/* soaX */);
        })));
      });
  }
},
_145/* identity2elementUpdated3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" does not exist"));
}),
_146/* identity2elementUpdated4 */ = new T2(1,_4q/* GHC.Show.shows5 */,_I/* GHC.Types.[] */),
_147/* $wa */ = function(_148/* sobE */, _149/* sobF */, _/* EXTERNAL */){
  var _14a/* sobH */ = B(_Ol/* FormEngine.FormElement.Updating.identity2element' */(_148/* sobE */, _149/* sobF */));
  if(!_14a/* sobH */._){
    var _14b/* sobK */ = new T(function(){
      return B(_12/* GHC.Base.++ */(new T2(1,_4q/* GHC.Show.shows5 */,new T(function(){
        return B(_6A/* GHC.Show.showLitString */(_148/* sobE */, _146/* FormEngine.FormElement.Updating.identity2elementUpdated4 */));
      })), _145/* FormEngine.FormElement.Updating.identity2elementUpdated3 */));
    }),
    _14c/* sobM */ = B(_8k/* FormEngine.JQuery.errorIO1 */(B(unAppCStr/* EXTERNAL */("identity2elementUpdated: element with identity=", _14b/* sobK */)), _/* EXTERNAL */));
    return _2o/* GHC.Base.Nothing */;
  }else{
    var _14d/* sobQ */ = B(_13f/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_14a/* sobH */.a, _/* EXTERNAL */));
    return new T1(1,_14d/* sobQ */);
  }
},
_14e/* setVal2 */ = "(function (val, jq) { jq.val(val).change(); return jq; })",
_14f/* $wa35 */ = function(_14g/* so4M */, _14h/* so4N */, _/* EXTERNAL */){
  var _14i/* so4X */ = eval/* EXTERNAL */(E(_14e/* FormEngine.JQuery.setVal2 */));
  return new F(function(){return E(_14i/* so4X */)(toJSStr/* EXTERNAL */(E(_14g/* so4M */)), _14h/* so4N */);});
},
_14j/* $fExceptionRecSelError_ww4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("RecSelError"));
}),
_14k/* $fExceptionRecSelError_wild */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_P0/* Control.Exception.Base.$fExceptionNestedAtomically_ww2 */,_P1/* Control.Exception.Base.$fExceptionNestedAtomically_ww4 */,_14j/* Control.Exception.Base.$fExceptionRecSelError_ww4 */),
_14l/* $fExceptionRecSelError2 */ = new T5(0,new Long/* EXTERNAL */(2975920724, 3651309139, true),new Long/* EXTERNAL */(465443624, 4160253997, true),_14k/* Control.Exception.Base.$fExceptionRecSelError_wild */,_I/* GHC.Types.[] */,_I/* GHC.Types.[] */),
_14m/* $fExceptionRecSelError1 */ = function(_14n/* s4nv0 */){
  return E(_14l/* Control.Exception.Base.$fExceptionRecSelError2 */);
},
_14o/* $fExceptionRecSelError_$cfromException */ = function(_14p/* s4nvr */){
  var _14q/* s4nvs */ = E(_14p/* s4nvr */);
  return new F(function(){return _O/* Data.Typeable.cast */(B(_M/* GHC.Exception.$p1Exception */(_14q/* s4nvs */.a)), _14m/* Control.Exception.Base.$fExceptionRecSelError1 */, _14q/* s4nvs */.b);});
},
_14r/* $fExceptionRecSelError_$cshow */ = function(_14s/* s4nvj */){
  return E(E(_14s/* s4nvj */).a);
},
_14t/* $fExceptionRecSelError_$ctoException */ = function(_Pd/* B1 */){
  return new T2(0,_14u/* Control.Exception.Base.$fExceptionRecSelError */,_Pd/* B1 */);
},
_14v/* $fShowRecSelError1 */ = function(_14w/* s4nqO */, _14x/* s4nqP */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_14w/* s4nqO */).a, _14x/* s4nqP */);});
},
_14y/* $fShowRecSelError_$cshowList */ = function(_14z/* s4nvh */, _14A/* s4nvi */){
  return new F(function(){return _26/* GHC.Show.showList__ */(_14v/* Control.Exception.Base.$fShowRecSelError1 */, _14z/* s4nvh */, _14A/* s4nvi */);});
},
_14B/* $fShowRecSelError_$cshowsPrec */ = function(_14C/* s4nvm */, _14D/* s4nvn */, _14E/* s4nvo */){
  return new F(function(){return _12/* GHC.Base.++ */(E(_14D/* s4nvn */).a, _14E/* s4nvo */);});
},
_14F/* $fShowRecSelError */ = new T3(0,_14B/* Control.Exception.Base.$fShowRecSelError_$cshowsPrec */,_14r/* Control.Exception.Base.$fExceptionRecSelError_$cshow */,_14y/* Control.Exception.Base.$fShowRecSelError_$cshowList */),
_14u/* $fExceptionRecSelError */ = new T(function(){
  return new T5(0,_14m/* Control.Exception.Base.$fExceptionRecSelError1 */,_14F/* Control.Exception.Base.$fShowRecSelError */,_14t/* Control.Exception.Base.$fExceptionRecSelError_$ctoException */,_14o/* Control.Exception.Base.$fExceptionRecSelError_$cfromException */,_14r/* Control.Exception.Base.$fExceptionRecSelError_$cshow */);
}),
_14G/* recSelError */ = function(_14H/* s4nwW */){
  var _14I/* s4nwY */ = new T(function(){
    return B(unAppCStr/* EXTERNAL */("No match in record selector ", new T(function(){
      return B(unCStr/* EXTERNAL */(_14H/* s4nwW */));
    })));
  });
  return new F(function(){return _Pu/* GHC.Exception.throw1 */(new T1(0,_14I/* s4nwY */), _14u/* Control.Exception.Base.$fExceptionRecSelError */);});
},
_14J/* neMaybeValue1 */ = new T(function(){
  return B(_14G/* Control.Exception.Base.recSelError */("neMaybeValue"));
}),
_14K/* $wgo */ = function(_14L/* soc7 */, _14M/* soc8 */){
  while(1){
    var _14N/* soc9 */ = E(_14L/* soc7 */);
    if(!_14N/* soc9 */._){
      return E(_14M/* soc8 */);
    }else{
      var _14O/* socb */ = _14N/* soc9 */.b,
      _14P/* socc */ = E(_14N/* soc9 */.a);
      if(_14P/* socc */._==4){
        var _14Q/* soci */ = E(_14P/* socc */.b);
        if(!_14Q/* soci */._){
          _14L/* soc7 */ = _14O/* socb */;
          continue;
        }else{
          var _14R/*  soc8 */ = _14M/* soc8 */+E(_14Q/* soci */.a)|0;
          _14L/* soc7 */ = _14O/* socb */;
          _14M/* soc8 */ = _14R/*  soc8 */;
          continue;
        }
      }else{
        return E(_14J/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
      }
    }
  }
},
_14S/* int2Float */ = function(_14T/* sc58 */){
  return E(_14T/* sc58 */);
},
_14U/* numberElem2TB1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("TB"));
}),
_14V/* numberElem2TB2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("PB"));
}),
_14W/* numberElem2TB3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MB"));
}),
_14X/* numberElem2TB4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("GB"));
}),
_14Y/* numberElem2TB */ = function(_14Z/* s68Q */){
  var _150/* s68R */ = E(_14Z/* s68Q */);
  if(_150/* s68R */._==4){
    var _151/* s68T */ = _150/* s68R */.b,
    _152/* s68W */ = E(_150/* s68R */.c);
    if(!_152/* s68W */._){
      return __Z/* EXTERNAL */;
    }else{
      var _153/* s68X */ = _152/* s68W */.a;
      if(!B(_Lg/* GHC.Base.eqString */(_153/* s68X */, _14X/* FormEngine.FormElement.FormElement.numberElem2TB4 */))){
        if(!B(_Lg/* GHC.Base.eqString */(_153/* s68X */, _14W/* FormEngine.FormElement.FormElement.numberElem2TB3 */))){
          if(!B(_Lg/* GHC.Base.eqString */(_153/* s68X */, _14V/* FormEngine.FormElement.FormElement.numberElem2TB2 */))){
            if(!B(_Lg/* GHC.Base.eqString */(_153/* s68X */, _14U/* FormEngine.FormElement.FormElement.numberElem2TB1 */))){
              return __Z/* EXTERNAL */;
            }else{
              var _154/* s692 */ = E(_151/* s68T */);
              return (_154/* s692 */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
                return B(_14S/* GHC.Float.RealFracMethods.int2Float */(_154/* s692 */.a));
              }));
            }
          }else{
            var _155/* s695 */ = E(_151/* s68T */);
            return (_155/* s695 */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
              return E(_155/* s695 */.a)*1000;
            }));
          }
        }else{
          var _156/* s69c */ = E(_151/* s68T */);
          return (_156/* s69c */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
            return E(_156/* s69c */.a)*1.0e-6;
          }));
        }
      }else{
        var _157/* s69j */ = E(_151/* s68T */);
        return (_157/* s69j */._==0) ? __Z/* EXTERNAL */ : new T1(1,new T(function(){
          return E(_157/* s69j */.a)*1.0e-3;
        }));
      }
    }
  }else{
    return __Z/* EXTERNAL */;
  }
},
_158/* $wgo1 */ = function(_159/* soct */, _15a/* socu */){
  while(1){
    var _15b/* socv */ = E(_159/* soct */);
    if(!_15b/* socv */._){
      return E(_15a/* socu */);
    }else{
      var _15c/* socx */ = _15b/* socv */.b,
      _15d/* socy */ = B(_14Y/* FormEngine.FormElement.FormElement.numberElem2TB */(_15b/* socv */.a));
      if(!_15d/* socy */._){
        _159/* soct */ = _15c/* socx */;
        continue;
      }else{
        var _15e/*  socu */ = _15a/* socu */+E(_15d/* socy */.a);
        _159/* soct */ = _15c/* socx */;
        _15a/* socu */ = _15e/*  socu */;
        continue;
      }
    }
  }
},
_15f/* disableJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("true"));
}),
_15g/* disableJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("readonly"));
}),
_15h/* disableJq6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#eee"));
}),
_15i/* disableJq7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("background-color"));
}),
_15j/* elementId */ = function(_15k/* s5Tz */){
  return new F(function(){return _4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_15k/* s5Tz */)))).b);});
},
_15l/* go */ = function(_15m/* soc1 */){
  while(1){
    var _15n/* soc2 */ = E(_15m/* soc1 */);
    if(!_15n/* soc2 */._){
      return false;
    }else{
      if(!E(_15n/* soc2 */.a)._){
        return true;
      }else{
        _15m/* soc1 */ = _15n/* soc2 */.b;
        continue;
      }
    }
  }
},
_15o/* go1 */ = function(_15p/* socn */){
  while(1){
    var _15q/* soco */ = E(_15p/* socn */);
    if(!_15q/* soco */._){
      return false;
    }else{
      if(!E(_15q/* soco */.a)._){
        return true;
      }else{
        _15p/* socn */ = _15q/* soco */.b;
        continue;
      }
    }
  }
},
_15r/* selectIn2 */ = "(function (elId, context) { return $(elId, context); })",
_15s/* $wa18 */ = function(_15t/* so8g */, _15u/* so8h */, _/* EXTERNAL */){
  var _15v/* so8r */ = eval/* EXTERNAL */(E(_15r/* FormEngine.JQuery.selectIn2 */));
  return new F(function(){return E(_15v/* so8r */)(toJSStr/* EXTERNAL */(E(_15t/* so8g */)), _15u/* so8h */);});
},
_15w/* flagPlaceId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_flagPlaceId"));
}),
_15x/* flagPlaceId */ = function(_15y/* skD8 */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_15y/* skD8 */)))).b)), _15w/* FormEngine.FormElement.Identifiers.flagPlaceId1 */);});
},
_15z/* inputFieldUpdate3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".validity-flag"));
}),
_15A/* inputFieldUpdate4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_15B/* invalidImg */ = function(_15C/* sjjI */){
  return E(E(_15C/* sjjI */).c);
},
_15D/* removeJq_f1 */ = new T(function(){
  return (function (jq) { var p = jq.parent(); jq.remove(); return p; });
}),
_15E/* validImg */ = function(_15F/* sjjN */){
  return E(E(_15F/* sjjN */).b);
},
_15G/* inputFieldUpdate2 */ = function(_15H/* so1H */, _15I/* so1I */, _15J/* so1J */, _/* EXTERNAL */){
  var _15K/* so1N */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_15A/* FormEngine.FormElement.Updating.inputFieldUpdate4 */, new T(function(){
    return B(_15x/* FormEngine.FormElement.Identifiers.flagPlaceId */(_15H/* so1H */));
  },1))), _/* EXTERNAL */)),
  _15L/* so1Q */ = E(_15K/* so1N */),
  _15M/* so1S */ = B(_15s/* FormEngine.JQuery.$wa18 */(_15z/* FormEngine.FormElement.Updating.inputFieldUpdate3 */, _15L/* so1Q */, _/* EXTERNAL */)),
  _15N/* so20 */ = __app1/* EXTERNAL */(E(_15D/* FormEngine.JQuery.removeJq_f1 */), E(_15M/* so1S */));
  if(!E(_15J/* so1J */)){
    if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_15H/* so1H */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _15O/* so2h */ = B(_Ky/* FormEngine.JQuery.$wa3 */(B(_15B/* FormEngine.FormContext.invalidImg */(_15I/* so1I */)), _15L/* so1Q */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }else{
    if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_15H/* so1H */)))).h)){
      return _0/* GHC.Tuple.() */;
    }else{
      var _15P/* so2x */ = B(_Ky/* FormEngine.JQuery.$wa3 */(B(_15E/* FormEngine.FormContext.validImg */(_15I/* so1I */)), _15L/* so1Q */, _/* EXTERNAL */));
      return _0/* GHC.Tuple.() */;
    }
  }
},
_15Q/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Rule application did not unify: "));
}),
_15R/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(" @"));
}),
_15S/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("invalid operand in "));
}),
_15T/* selectByIdentity2 */ = "(function (identity) { return $(\'[identity=\"\' + identity + \'\"]\'); })",
_15U/* selectByIdentity1 */ = function(_15V/* snUV */, _/* EXTERNAL */){
  var _15W/* snV5 */ = eval/* EXTERNAL */(E(_15T/* FormEngine.JQuery.selectByIdentity2 */));
  return new F(function(){return E(_15W/* snV5 */)(toJSStr/* EXTERNAL */(E(_15V/* snUV */)));});
},
_15X/* applyRule1 */ = function(_15Y/* socD */, _15Z/* socE */, _160/* socF */, _/* EXTERNAL */){
  var _161/* socH */ = function(_/* EXTERNAL */){
    var _162/* socJ */ = E(_160/* socF */);
    switch(_162/* socJ */._){
      case 2:
        var _163/* socR */ = B(_15U/* FormEngine.JQuery.selectByIdentity1 */(_162/* socJ */.a, _/* EXTERNAL */)),
        _164/* socZ */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_163/* socR */)),
        _165/* sod2 */ = B(_15U/* FormEngine.JQuery.selectByIdentity1 */(_162/* socJ */.b, _/* EXTERNAL */)),
        _166/* sod6 */ = String/* EXTERNAL */(_164/* socZ */),
        _167/* sodf */ = B(_14f/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_166/* sod6 */), E(_165/* sod2 */), _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 3:
        var _168/* sodj */ = B(_OX/* FormEngine.JQuery.selectByName1 */(B(_15j/* FormEngine.FormElement.FormElement.elementId */(_15Y/* socD */)), _/* EXTERNAL */)),
        _169/* sodm */ = E(_168/* sodj */),
        _16a/* sodo */ = B(_77/* FormEngine.JQuery.$wa2 */(_15i/* FormEngine.JQuery.disableJq7 */, _15h/* FormEngine.JQuery.disableJq6 */, _169/* sodm */, _/* EXTERNAL */)),
        _16b/* sodr */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_15g/* FormEngine.JQuery.disableJq3 */, _15f/* FormEngine.JQuery.disableJq2 */, _169/* sodm */, _/* EXTERNAL */));
        return _0/* GHC.Tuple.() */;
      case 4:
        var _16c/* sodv */ = B(_13f/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_15Y/* socD */, _/* EXTERNAL */)),
        _16d/* sody */ = E(_16c/* sodv */);
        if(_16d/* sody */._==4){
          var _16e/* sodE */ = E(_16d/* sody */.b);
          if(!_16e/* sodE */._){
            return new F(function(){return _15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_16d/* sody */, _15Z/* socE */, _2G/* GHC.Types.False */, _/* EXTERNAL */);});
          }else{
            return new F(function(){return _15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_16d/* sody */, _15Z/* socE */, new T(function(){
              return B(A1(_162/* socJ */.a,_16e/* sodE */.a));
            },1), _/* EXTERNAL */);});
          }
        }else{
          return E(_14J/* FormEngine.FormElement.FormElement.neMaybeValue1 */);
        }
        break;
      default:
        var _16f/* socN */ = new T(function(){
          var _16g/* socM */ = new T(function(){
            return B(_12/* GHC.Base.++ */(_15R/* FormEngine.FormElement.Updating.lvl4 */, new T(function(){
              return B(_6G/* FormEngine.FormElement.FormElement.$fShowFormElement_$cshow */(_15Y/* socD */));
            },1)));
          },1);
          return B(_12/* GHC.Base.++ */(B(_Oc/* FormEngine.FormItem.$fShowFormRule_$cshow */(_162/* socJ */)), _16g/* socM */));
        },1);
        return new F(function(){return _8k/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_15Q/* FormEngine.FormElement.Updating.lvl3 */, _16f/* socN */)), _/* EXTERNAL */);});
    }
  };
  if(E(_15Y/* socD */)._==4){
    var _16h/* sodM */ = E(_160/* socF */);
    switch(_16h/* sodM */._){
      case 0:
        var _16i/* sodP */ = function(_/* EXTERNAL */, _16j/* sodR */){
          if(!B(_15l/* FormEngine.FormElement.Updating.go */(_16j/* sodR */))){
            var _16k/* sodT */ = B(_15U/* FormEngine.JQuery.selectByIdentity1 */(_16h/* sodM */.b, _/* EXTERNAL */)),
            _16l/* soe1 */ = B(_14f/* FormEngine.JQuery.$wa35 */(B(_4a/* GHC.Show.$wshowSignedInt */(0, B(_14K/* FormEngine.FormElement.Updating.$wgo */(B(_87/* Data.Maybe.catMaybes1 */(_16j/* sodR */)), 0)), _I/* GHC.Types.[] */)), E(_16k/* sodT */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _16m/* soe6 */ = B(_8k/* FormEngine.JQuery.errorIO1 */(B(_12/* GHC.Base.++ */(_15S/* FormEngine.FormElement.Updating.lvl5 */, new T(function(){
              return B(_Oc/* FormEngine.FormItem.$fShowFormRule_$cshow */(_16h/* sodM */));
            },1))), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        },
        _16n/* soe9 */ = E(_16h/* sodM */.a);
        if(!_16n/* soe9 */._){
          return new F(function(){return _16i/* sodP */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _16o/* soed */ = E(_15Z/* socE */).a,
          _16p/* soeg */ = B(_147/* FormEngine.FormElement.Updating.$wa */(_16n/* soe9 */.a, _16o/* soed */, _/* EXTERNAL */)),
          _16q/* soej */ = function(_16r/* soek */, _/* EXTERNAL */){
            var _16s/* soem */ = E(_16r/* soek */);
            if(!_16s/* soem */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _16t/* soep */ = B(_147/* FormEngine.FormElement.Updating.$wa */(_16s/* soem */.a, _16o/* soed */, _/* EXTERNAL */)),
              _16u/* soes */ = B(_16q/* soej */(_16s/* soem */.b, _/* EXTERNAL */));
              return new T2(1,_16t/* soep */,_16u/* soes */);
            }
          },
          _16v/* soew */ = B(_16q/* soej */(_16n/* soe9 */.b, _/* EXTERNAL */));
          return new F(function(){return _16i/* sodP */(_/* EXTERNAL */, new T2(1,_16p/* soeg */,_16v/* soew */));});
        }
        break;
      case 1:
        var _16w/* soeC */ = function(_/* EXTERNAL */, _16x/* soeE */){
          if(!B(_15o/* FormEngine.FormElement.Updating.go1 */(_16x/* soeE */))){
            var _16y/* soeG */ = B(_15U/* FormEngine.JQuery.selectByIdentity1 */(_16h/* sodM */.b, _/* EXTERNAL */)),
            _16z/* soeM */ = jsShow/* EXTERNAL */(B(_158/* FormEngine.FormElement.Updating.$wgo1 */(B(_87/* Data.Maybe.catMaybes1 */(_16x/* soeE */)), 0))),
            _16A/* soeT */ = B(_14f/* FormEngine.JQuery.$wa35 */(fromJSStr/* EXTERNAL */(_16z/* soeM */), E(_16y/* soeG */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            return _0/* GHC.Tuple.() */;
          }
        },
        _16B/* soeW */ = E(_16h/* sodM */.a);
        if(!_16B/* soeW */._){
          return new F(function(){return _16w/* soeC */(_/* EXTERNAL */, _I/* GHC.Types.[] */);});
        }else{
          var _16C/* sof0 */ = E(_15Z/* socE */).a,
          _16D/* sof3 */ = B(_147/* FormEngine.FormElement.Updating.$wa */(_16B/* soeW */.a, _16C/* sof0 */, _/* EXTERNAL */)),
          _16E/* sof6 */ = function(_16F/* sof7 */, _/* EXTERNAL */){
            var _16G/* sof9 */ = E(_16F/* sof7 */);
            if(!_16G/* sof9 */._){
              return _I/* GHC.Types.[] */;
            }else{
              var _16H/* sofc */ = B(_147/* FormEngine.FormElement.Updating.$wa */(_16G/* sof9 */.a, _16C/* sof0 */, _/* EXTERNAL */)),
              _16I/* soff */ = B(_16E/* sof6 */(_16G/* sof9 */.b, _/* EXTERNAL */));
              return new T2(1,_16H/* sofc */,_16I/* soff */);
            }
          },
          _16J/* sofj */ = B(_16E/* sof6 */(_16B/* soeW */.b, _/* EXTERNAL */));
          return new F(function(){return _16w/* soeC */(_/* EXTERNAL */, new T2(1,_16D/* sof3 */,_16J/* sofj */));});
        }
        break;
      default:
        return new F(function(){return _161/* socH */(_/* EXTERNAL */);});
    }
  }else{
    return new F(function(){return _161/* socH */(_/* EXTERNAL */);});
  }
},
_16K/* applyRules1 */ = function(_16L/* sofn */, _16M/* sofo */, _/* EXTERNAL */){
  var _16N/* sofB */ = function(_16O/* sofC */, _/* EXTERNAL */){
    while(1){
      var _16P/* sofE */ = E(_16O/* sofC */);
      if(!_16P/* sofE */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _16Q/* sofH */ = B(_15X/* FormEngine.FormElement.Updating.applyRule1 */(_16L/* sofn */, _16M/* sofo */, _16P/* sofE */.a, _/* EXTERNAL */));
        _16O/* sofC */ = _16P/* sofE */.b;
        continue;
      }
    }
  };
  return new F(function(){return _16N/* sofB */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_16L/* sofn */)))).i, _/* EXTERNAL */);});
},
_16R/* isJust */ = function(_16S/* s7rZ */){
  return (E(_16S/* s7rZ */)._==0) ? false : true;
},
_16T/* nfiUnit1 */ = new T(function(){
  return B(_14G/* Control.Exception.Base.recSelError */("nfiUnit"));
}),
_16U/* go */ = function(_16V/* sjKR */){
  while(1){
    var _16W/* sjKS */ = E(_16V/* sjKR */);
    if(!_16W/* sjKS */._){
      return true;
    }else{
      if(!E(_16W/* sjKS */.a)){
        return false;
      }else{
        _16V/* sjKR */ = _16W/* sjKS */.b;
        continue;
      }
    }
  }
},
_16X/* validateElement3 */ = new T(function(){
  return B(_PT/* Control.Exception.Base.patError */("FormEngine/FormElement/Validation.hs:(19,1)-(51,41)|function validateElement"));
}),
_16Y/* validateElement_go */ = function(_16Z/* sjKA */){
  while(1){
    var _170/* sjKB */ = E(_16Z/* sjKA */);
    if(!_170/* sjKB */._){
      return false;
    }else{
      var _171/* sjKD */ = _170/* sjKB */.b,
      _172/* sjKE */ = E(_170/* sjKB */.a);
      if(!_172/* sjKE */._){
        if(!E(_172/* sjKE */.b)){
          _16Z/* sjKA */ = _171/* sjKD */;
          continue;
        }else{
          return true;
        }
      }else{
        if(!E(_172/* sjKE */.b)){
          _16Z/* sjKA */ = _171/* sjKD */;
          continue;
        }else{
          return true;
        }
      }
    }
  }
},
_173/* validateElement_go1 */ = function(_174/* sjKM */){
  while(1){
    var _175/* sjKN */ = E(_174/* sjKM */);
    if(!_175/* sjKN */._){
      return true;
    }else{
      if(!E(_175/* sjKN */.a)){
        return false;
      }else{
        _174/* sjKM */ = _175/* sjKN */.b;
        continue;
      }
    }
  }
},
_176/* go1 */ = function(_177/*  sjL3 */){
  while(1){
    var _178/*  go1 */ = B((function(_179/* sjL3 */){
      var _17a/* sjL4 */ = E(_179/* sjL3 */);
      if(!_17a/* sjL4 */._){
        return __Z/* EXTERNAL */;
      }else{
        var _17b/* sjL6 */ = _17a/* sjL4 */.b,
        _17c/* sjL7 */ = E(_17a/* sjL4 */.a);
        switch(_17c/* sjL7 */._){
          case 0:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_17d/* FormEngine.FormElement.Validation.validateElement2 */(_17c/* sjL7 */.b));
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 1:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17c/* sjL7 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 2:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17c/* sjL7 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 3:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17c/* sjL7 */.b, _I/* GHC.Types.[] */))){
                  return true;
                }else{
                  return false;
                }
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 4:
            var _17e/* sjMd */ = _17c/* sjL7 */.a;
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17e/* sjMd */)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                var _17f/* sjMs */ = E(_17c/* sjL7 */.b);
                if(!_17f/* sjMs */._){
                  return false;
                }else{
                  if(E(_17f/* sjMs */.a)<0){
                    return false;
                  }else{
                    var _17g/* sjMy */ = E(_17e/* sjMd */);
                    if(_17g/* sjMy */._==3){
                      if(E(_17g/* sjMy */.b)._==1){
                        return B(_16R/* Data.Maybe.isJust */(_17c/* sjL7 */.c));
                      }else{
                        return true;
                      }
                    }else{
                      return E(_16T/* FormEngine.FormItem.nfiUnit1 */);
                    }
                  }
                }
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 5:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_16X/* FormEngine.FormElement.Validation.validateElement3 */,new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 6:
            var _17h/* sjMU */ = _17c/* sjL7 */.a,
            _17i/* sjMV */ = _17c/* sjL7 */.b;
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17h/* sjMU */)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17h/* sjMU */)).h)){
                  return B(_173/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_17j/* FormEngine.FormElement.Validation.validateElement1 */, _17i/* sjMV */))));
                }else{
                  if(!B(_16Y/* FormEngine.FormElement.Validation.validateElement_go */(_17i/* sjMV */))){
                    return false;
                  }else{
                    return B(_173/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_17j/* FormEngine.FormElement.Validation.validateElement1 */, _17i/* sjMV */))));
                  }
                }
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 7:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_16R/* Data.Maybe.isJust */(_17c/* sjL7 */.b));
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 8:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_17d/* FormEngine.FormElement.Validation.validateElement2 */(_17c/* sjL7 */.b));
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 9:
            return new T2(1,new T(function(){
              if(!E(_17c/* sjL7 */.b)){
                return true;
              }else{
                return B(_17d/* FormEngine.FormElement.Validation.validateElement2 */(_17c/* sjL7 */.c));
              }
            }),new T(function(){
              return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
            }));
          case 10:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,new T(function(){
                return B(_17d/* FormEngine.FormElement.Validation.validateElement2 */(_17c/* sjL7 */.b));
              }),new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          case 11:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_aC/* GHC.Types.True */,new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
            break;
          default:
            if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17c/* sjL7 */.a)).h)){
              _177/*  sjL3 */ = _17b/* sjL6 */;
              return __continue/* EXTERNAL */;
            }else{
              return new T2(1,_aC/* GHC.Types.True */,new T(function(){
                return B(_176/* FormEngine.FormElement.Validation.go1 */(_17b/* sjL6 */));
              }));
            }
        }
      }
    })(_177/*  sjL3 */));
    if(_178/*  go1 */!=__continue/* EXTERNAL */){
      return _178/*  go1 */;
    }
  }
},
_17d/* validateElement2 */ = function(_17k/* sjOJ */){
  return new F(function(){return _16U/* FormEngine.FormElement.Validation.go */(B(_176/* FormEngine.FormElement.Validation.go1 */(_17k/* sjOJ */)));});
},
_17j/* validateElement1 */ = function(_17l/* sjKW */){
  var _17m/* sjKX */ = E(_17l/* sjKW */);
  if(!_17m/* sjKX */._){
    return true;
  }else{
    return new F(function(){return _17d/* FormEngine.FormElement.Validation.validateElement2 */(_17m/* sjKX */.c);});
  }
},
_17n/* validateElement */ = function(_17o/* sjOL */){
  var _17p/* sjOM */ = E(_17o/* sjOL */);
  switch(_17p/* sjOM */._){
    case 0:
      return new F(function(){return _17d/* FormEngine.FormElement.Validation.validateElement2 */(_17p/* sjOM */.b);});
      break;
    case 1:
      return (!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17p/* sjOM */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 2:
      return (!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17p/* sjOM */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 3:
      return (!B(_QH/* GHC.Classes.$fEq[]_$s$c==1 */(_17p/* sjOM */.b, _I/* GHC.Types.[] */))) ? true : false;
    case 4:
      var _17q/* sjP6 */ = E(_17p/* sjOM */.b);
      if(!_17q/* sjP6 */._){
        return false;
      }else{
        if(E(_17q/* sjP6 */.a)<0){
          return false;
        }else{
          var _17r/* sjPc */ = E(_17p/* sjOM */.a);
          if(_17r/* sjPc */._==3){
            if(E(_17r/* sjPc */.b)._==1){
              return new F(function(){return _16R/* Data.Maybe.isJust */(_17p/* sjOM */.c);});
            }else{
              return true;
            }
          }else{
            return E(_16T/* FormEngine.FormItem.nfiUnit1 */);
          }
        }
      }
      break;
    case 5:
      return E(_16X/* FormEngine.FormElement.Validation.validateElement3 */);
    case 6:
      var _17s/* sjPl */ = _17p/* sjOM */.b;
      if(!E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_17p/* sjOM */.a)).h)){
        return new F(function(){return _173/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_17j/* FormEngine.FormElement.Validation.validateElement1 */, _17s/* sjPl */)));});
      }else{
        if(!B(_16Y/* FormEngine.FormElement.Validation.validateElement_go */(_17s/* sjPl */))){
          return false;
        }else{
          return new F(function(){return _173/* FormEngine.FormElement.Validation.validateElement_go1 */(B(_2S/* GHC.Base.map */(_17j/* FormEngine.FormElement.Validation.validateElement1 */, _17s/* sjPl */)));});
        }
      }
      break;
    case 7:
      return new F(function(){return _16R/* Data.Maybe.isJust */(_17p/* sjOM */.b);});
      break;
    case 8:
      return new F(function(){return _17d/* FormEngine.FormElement.Validation.validateElement2 */(_17p/* sjOM */.b);});
      break;
    case 9:
      if(!E(_17p/* sjOM */.b)){
        return true;
      }else{
        return new F(function(){return _17d/* FormEngine.FormElement.Validation.validateElement2 */(_17p/* sjOM */.c);});
      }
      break;
    case 10:
      return new F(function(){return _17d/* FormEngine.FormElement.Validation.validateElement2 */(_17p/* sjOM */.b);});
      break;
    case 11:
      return true;
    default:
      return true;
  }
},
_17t/* $wa */ = function(_17u/* s8XL */, _17v/* s8XM */, _17w/* s8XN */, _/* EXTERNAL */){
  var _17x/* s8XP */ = B(_13f/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_17u/* s8XL */, _/* EXTERNAL */)),
  _17y/* s8XT */ = B(_15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_17x/* s8XP */, _17v/* s8XM */, new T(function(){
    return B(_17n/* FormEngine.FormElement.Validation.validateElement */(_17x/* s8XP */));
  },1), _/* EXTERNAL */)),
  _17z/* s8XW */ = B(_16K/* FormEngine.FormElement.Updating.applyRules1 */(_17u/* s8XL */, _17v/* s8XM */, _/* EXTERNAL */)),
  _17A/* s8Y3 */ = E(E(_17w/* s8XN */).b);
  if(!_17A/* s8Y3 */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_17A/* s8Y3 */.a,_17u/* s8XL */, _17v/* s8XM */, _/* EXTERNAL */);});
  }
},
_17B/* $wa1 */ = function(_17C/* s8Y5 */, _17D/* s8Y6 */, _17E/* s8Y7 */, _/* EXTERNAL */){
  var _17F/* s8Y9 */ = B(_13f/* FormEngine.FormElement.Updating.identity2elementUpdated2 */(_17C/* s8Y5 */, _/* EXTERNAL */)),
  _17G/* s8Yd */ = B(_15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_17F/* s8Y9 */, _17D/* s8Y6 */, new T(function(){
    return B(_17n/* FormEngine.FormElement.Validation.validateElement */(_17F/* s8Y9 */));
  },1), _/* EXTERNAL */)),
  _17H/* s8Yg */ = B(_16K/* FormEngine.FormElement.Updating.applyRules1 */(_17C/* s8Y5 */, _17D/* s8Y6 */, _/* EXTERNAL */)),
  _17I/* s8Yn */ = E(E(_17E/* s8Y7 */).a);
  if(!_17I/* s8Yn */._){
    return _0/* GHC.Tuple.() */;
  }else{
    return new F(function(){return A3(_17I/* s8Yn */.a,_17C/* s8Y5 */, _17D/* s8Y6 */, _/* EXTERNAL */);});
  }
},
_17J/* $wa1 */ = function(_17K/* so1y */, _17L/* so1z */, _/* EXTERNAL */){
  var _17M/* so1E */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_17L/* so1z */),
  _17N/* so1K */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_17M/* so1E */),
  _17O/* so1V */ = eval/* EXTERNAL */(E(_K5/* FormEngine.JQuery.addClass2 */)),
  _17P/* so23 */ = E(_17O/* so1V */)(toJSStr/* EXTERNAL */(E(_17K/* so1y */)), _17N/* so1K */);
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(_17P/* so23 */);});
},
_17Q/* $wa23 */ = function(_17R/* snP5 */, _17S/* snP6 */, _/* EXTERNAL */){
  var _17T/* snPb */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_17S/* snP6 */),
  _17U/* snPh */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_17T/* snPb */),
  _17V/* snPl */ = B(_KW/* FormEngine.JQuery.onClick1 */(_17R/* snP5 */, _17U/* snPh */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_17V/* snPl */));});
},
_17W/* onMouseEnter2 */ = "(function (ev, jq) { jq.mouseenter(ev); })",
_17X/* onMouseEnter1 */ = function(_17Y/* snEt */, _17Z/* snEu */, _/* EXTERNAL */){
  var _180/* snEG */ = __createJSFunc/* EXTERNAL */(2, function(_181/* snEx */, _/* EXTERNAL */){
    var _182/* snEz */ = B(A2(E(_17Y/* snEt */),_181/* snEx */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _183/* snEJ */ = E(_17Z/* snEu */),
  _184/* snEO */ = eval/* EXTERNAL */(E(_17W/* FormEngine.JQuery.onMouseEnter2 */)),
  _185/* snEW */ = E(_184/* snEO */)(_180/* snEG */, _183/* snEJ */);
  return _183/* snEJ */;
},
_186/* $wa30 */ = function(_187/* snPC */, _188/* snPD */, _/* EXTERNAL */){
  var _189/* snPI */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_188/* snPD */),
  _18a/* snPO */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_189/* snPI */),
  _18b/* snPS */ = B(_17X/* FormEngine.JQuery.onMouseEnter1 */(_187/* snPC */, _18a/* snPO */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_18b/* snPS */));});
},
_18c/* onMouseLeave2 */ = "(function (ev, jq) { jq.mouseleave(ev); })",
_18d/* onMouseLeave1 */ = function(_18e/* snDU */, _18f/* snDV */, _/* EXTERNAL */){
  var _18g/* snE7 */ = __createJSFunc/* EXTERNAL */(2, function(_18h/* snDY */, _/* EXTERNAL */){
    var _18i/* snE0 */ = B(A2(E(_18e/* snDU */),_18h/* snDY */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _18j/* snEa */ = E(_18f/* snDV */),
  _18k/* snEf */ = eval/* EXTERNAL */(E(_18c/* FormEngine.JQuery.onMouseLeave2 */)),
  _18l/* snEn */ = E(_18k/* snEf */)(_18g/* snE7 */, _18j/* snEa */);
  return _18j/* snEa */;
},
_18m/* $wa31 */ = function(_18n/* snQ9 */, _18o/* snQa */, _/* EXTERNAL */){
  var _18p/* snQf */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */)(_18o/* snQa */),
  _18q/* snQl */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */)(_18p/* snQf */),
  _18r/* snQp */ = B(_18d/* FormEngine.JQuery.onMouseLeave1 */(_18n/* snQ9 */, _18q/* snQl */, _/* EXTERNAL */));
  return new F(function(){return E(_Kg/* FormEngine.JQuery.addClassInside_f1 */)(E(_18r/* snQp */));});
},
_18s/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span class=\'short-desc\'>"));
}),
_18t/* setTextInside1 */ = function(_18u/* so7D */, _18v/* so7E */, _/* EXTERNAL */){
  return new F(function(){return _KD/* FormEngine.JQuery.$wa34 */(_18u/* so7D */, E(_18v/* so7E */), _/* EXTERNAL */);});
},
_18w/* a1 */ = function(_18x/* s8WW */, _18y/* s8WX */, _/* EXTERNAL */){
  var _18z/* s8Xa */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_18x/* s8WW */)))).e);
  if(!_18z/* s8Xa */._){
    return _18y/* s8WX */;
  }else{
    var _18A/* s8Xe */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18s/* FormEngine.FormElement.Rendering.lvl */, E(_18y/* s8WX */), _/* EXTERNAL */));
    return new F(function(){return _18t/* FormEngine.JQuery.setTextInside1 */(_18z/* s8Xa */.a, _18A/* s8Xe */, _/* EXTERNAL */);});
  }
},
_18B/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label>"));
}),
_18C/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<label class=\"link\" onclick=\""));
}),
_18D/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\">"));
}),
_18E/* a2 */ = function(_18F/* s8Xh */, _18G/* s8Xi */, _/* EXTERNAL */){
  var _18H/* s8Xl */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_18F/* s8Xh */)))),
  _18I/* s8Xv */ = E(_18H/* s8Xl */.a);
  if(!_18I/* s8Xv */._){
    return _18G/* s8Xi */;
  }else{
    var _18J/* s8Xw */ = _18I/* s8Xv */.a,
    _18K/* s8Xx */ = E(_18H/* s8Xl */.g);
    if(!_18K/* s8Xx */._){
      var _18L/* s8XA */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, E(_18G/* s8Xi */), _/* EXTERNAL */));
      return new F(function(){return _18t/* FormEngine.JQuery.setTextInside1 */(_18J/* s8Xw */, _18L/* s8XA */, _/* EXTERNAL */);});
    }else{
      var _18M/* s8XI */ = B(_Ky/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_18C/* FormEngine.FormElement.Rendering.lvl2 */, new T(function(){
        return B(_12/* GHC.Base.++ */(_18K/* s8Xx */.a, _18D/* FormEngine.FormElement.Rendering.lvl3 */));
      },1))), E(_18G/* s8Xi */), _/* EXTERNAL */));
      return new F(function(){return _18t/* FormEngine.JQuery.setTextInside1 */(_18J/* s8Xw */, _18M/* s8XI */, _/* EXTERNAL */);});
    }
  }
},
_18N/* a3 */ = function(_18O/* s8Yp */, _/* EXTERNAL */){
  var _18P/* s8Yt */ = B(_7v/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_NT/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_18O/* s8Yp */));
  }))), _/* EXTERNAL */)),
  _18Q/* s8Yy */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, E(_18P/* s8Yt */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_18R/* findSelector2 */ = "(function (elJs, jq) { return jq.find(elJs); })",
_18S/* $wa9 */ = function(_18T/* so7L */, _18U/* so7M */, _/* EXTERNAL */){
  var _18V/* so7W */ = eval/* EXTERNAL */(E(_18R/* FormEngine.JQuery.findSelector2 */));
  return new F(function(){return E(_18V/* so7W */)(toJSStr/* EXTERNAL */(E(_18T/* so7L */)), _18U/* so7M */);});
},
_18W/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("span"));
}),
_18X/* a4 */ = function(_18Y/* s8YB */, _/* EXTERNAL */){
  var _18Z/* s8YF */ = B(_7v/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", new T(function(){
    return B(_NT/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_18Y/* s8YB */));
  }))), _/* EXTERNAL */)),
  _190/* s8YI */ = E(_18Z/* s8YF */),
  _191/* s8YK */ = B(_18S/* FormEngine.JQuery.$wa9 */(_18W/* FormEngine.FormElement.Rendering.lvl4 */, _190/* s8YI */, _/* EXTERNAL */)),
  _192/* s8YY */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_18Y/* s8YB */)))).f);
  if(!_192/* s8YY */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _193/* s8Z2 */ = B(_Ni/* FormEngine.JQuery.$wa26 */(_192/* s8YY */.a, E(_191/* s8YK */), _/* EXTERNAL */)),
    _194/* s8Z5 */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _Le/* FormEngine.JQuery.appearJq2 */, _190/* s8YI */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_195/* funcImg */ = function(_196/* sjop */){
  return E(E(_196/* sjop */).a);
},
_197/* lvl10 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd\'>"));
}),
_198/* lvl11 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_199/* lvl5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table>"));
}),
_19a/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tbody>"));
}),
_19b/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<tr>"));
}),
_19c/* lvl8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td>"));
}),
_19d/* lvl9 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("more-space"));
}),
_19e/* $wa2 */ = function(_19f/* s8Z8 */, _19g/* s8Z9 */, _19h/* s8Za */, _19i/* s8Zb */, _19j/* s8Zc */, _/* EXTERNAL */){
  var _19k/* s8Ze */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_199/* FormEngine.FormElement.Rendering.lvl5 */, _19j/* s8Zc */, _/* EXTERNAL */)),
  _19l/* s8Zm */ = B(_186/* FormEngine.JQuery.$wa30 */(function(_19m/* s8Zj */, _/* EXTERNAL */){
    return new F(function(){return _18X/* FormEngine.FormElement.Rendering.a4 */(_19g/* s8Z9 */, _/* EXTERNAL */);});
  }, E(_19k/* s8Ze */), _/* EXTERNAL */)),
  _19n/* s8Zu */ = B(_18m/* FormEngine.JQuery.$wa31 */(function(_19o/* s8Zr */, _/* EXTERNAL */){
    return new F(function(){return _18N/* FormEngine.FormElement.Rendering.a3 */(_19g/* s8Z9 */, _/* EXTERNAL */);});
  }, E(_19l/* s8Zm */), _/* EXTERNAL */)),
  _19p/* s8Zz */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
  _19q/* s8ZC */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19n/* s8Zu */)),
  _19r/* s8ZF */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
  _19s/* s8ZI */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19q/* s8ZC */),
  _19t/* s8ZL */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19a/* FormEngine.FormElement.Rendering.lvl6 */, _19s/* s8ZI */, _/* EXTERNAL */)),
  _19u/* s8ZR */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19t/* s8ZL */)),
  _19v/* s8ZV */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19u/* s8ZR */),
  _19w/* s8ZY */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19b/* FormEngine.FormElement.Rendering.lvl7 */, _19v/* s8ZV */, _/* EXTERNAL */)),
  _19x/* s904 */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19w/* s8ZY */)),
  _19y/* s908 */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19x/* s904 */),
  _19z/* s90f */ = function(_/* EXTERNAL */, _19A/* s90h */){
    var _19B/* s90i */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_197/* FormEngine.FormElement.Rendering.lvl10 */, _19A/* s90h */, _/* EXTERNAL */)),
    _19C/* s90o */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19B/* s90i */)),
    _19D/* s90s */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19C/* s90o */),
    _19E/* s90v */ = B(_K6/* FormEngine.JQuery.$wa */(_19d/* FormEngine.FormElement.Rendering.lvl9 */, _19D/* s90s */, _/* EXTERNAL */)),
    _19F/* s90y */ = B(_18E/* FormEngine.FormElement.Rendering.a2 */(_19g/* s8Z9 */, _19E/* s90v */, _/* EXTERNAL */)),
    _19G/* s90D */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
    _19H/* s90G */ = __app1/* EXTERNAL */(_19G/* s90D */, E(_19F/* s90y */)),
    _19I/* s90J */ = B(A1(_19f/* s8Z8 */,_/* EXTERNAL */)),
    _19J/* s90M */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19c/* FormEngine.FormElement.Rendering.lvl8 */, _19H/* s90G */, _/* EXTERNAL */)),
    _19K/* s90S */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19J/* s90M */)),
    _19L/* s90W */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19K/* s90S */),
    _19M/* s914 */ = __app2/* EXTERNAL */(E(_KK/* FormEngine.JQuery.appendJq_f1 */), E(_19I/* s90J */), _19L/* s90W */),
    _19N/* s918 */ = __app1/* EXTERNAL */(_19G/* s90D */, _19M/* s914 */),
    _19O/* s91b */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19c/* FormEngine.FormElement.Rendering.lvl8 */, _19N/* s918 */, _/* EXTERNAL */)),
    _19P/* s91h */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
      return B(_15x/* FormEngine.FormElement.Identifiers.flagPlaceId */(_19g/* s8Z9 */));
    },1), E(_19O/* s91b */), _/* EXTERNAL */)),
    _19Q/* s91n */ = __app1/* EXTERNAL */(_19G/* s90D */, E(_19P/* s91h */)),
    _19R/* s91r */ = __app1/* EXTERNAL */(_19G/* s90D */, _19Q/* s91n */),
    _19S/* s91v */ = __app1/* EXTERNAL */(_19G/* s90D */, _19R/* s91r */);
    return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a1 */(_19g/* s8Z9 */, _19S/* s91v */, _/* EXTERNAL */);});
  },
  _19T/* s91z */ = E(E(_19i/* s8Zb */).c);
  if(!_19T/* s91z */._){
    return new F(function(){return _19z/* s90f */(_/* EXTERNAL */, _19y/* s908 */);});
  }else{
    var _19U/* s91A */ = _19T/* s91z */.a,
    _19V/* s91B */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19c/* FormEngine.FormElement.Rendering.lvl8 */, _19y/* s908 */, _/* EXTERNAL */)),
    _19W/* s91H */ = __app1/* EXTERNAL */(_19p/* s8Zz */, E(_19V/* s91B */)),
    _19X/* s91L */ = __app1/* EXTERNAL */(_19r/* s8ZF */, _19W/* s91H */),
    _19Y/* s91O */ = B(_K6/* FormEngine.JQuery.$wa */(_19d/* FormEngine.FormElement.Rendering.lvl9 */, _19X/* s91L */, _/* EXTERNAL */)),
    _19Z/* s91U */ = B(_Ky/* FormEngine.JQuery.$wa3 */(B(_195/* FormEngine.Functionality.funcImg */(_19U/* s91A */)), E(_19Y/* s91O */), _/* EXTERNAL */)),
    _1a0/* s91Z */ = new T(function(){
      return B(A2(E(_19U/* s91A */).b,_19g/* s8Z9 */, _19h/* s8Za */));
    }),
    _1a1/* s925 */ = B(_17Q/* FormEngine.JQuery.$wa23 */(function(_1a2/* s923 */){
      return E(_1a0/* s91Z */);
    }, E(_19Z/* s91U */), _/* EXTERNAL */)),
    _1a3/* s92d */ = __app1/* EXTERNAL */(E(_Kg/* FormEngine.JQuery.addClassInside_f1 */), E(_1a1/* s925 */));
    return new F(function(){return _19z/* s90f */(_/* EXTERNAL */, _1a3/* s92d */);});
  }
},
_1a4/* a5 */ = function(_1a5/* s92l */, _/* EXTERNAL */){
  while(1){
    var _1a6/* s92n */ = E(_1a5/* s92l */);
    if(!_1a6/* s92n */._){
      return _0/* GHC.Tuple.() */;
    }else{
      var _1a7/* s92s */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, E(_1a6/* s92n */.a), _/* EXTERNAL */));
      _1a5/* s92l */ = _1a6/* s92n */.b;
      continue;
    }
  }
},
_1a8/* appendT1 */ = function(_1a9/* so0t */, _1aa/* so0u */, _/* EXTERNAL */){
  return new F(function(){return _Ky/* FormEngine.JQuery.$wa3 */(_1a9/* so0t */, E(_1aa/* so0u */), _/* EXTERNAL */);});
},
_1ab/* checkboxId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_optional_group"));
}),
_1ac/* checkboxId */ = function(_1ad/* skC0 */){
  return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_1ad/* skC0 */)))).b)), _1ab/* FormEngine.FormElement.Identifiers.checkboxId1 */);});
},
_1ae/* errorjq1 */ = function(_1af/* snJM */, _1ag/* snJN */, _/* EXTERNAL */){
  var _1ah/* snJX */ = eval/* EXTERNAL */(E(_8j/* FormEngine.JQuery.errorIO2 */)),
  _1ai/* snK5 */ = E(_1ah/* snJX */)(toJSStr/* EXTERNAL */(E(_1af/* snJM */)));
  return _1ag/* snJN */;
},
_1aj/* go */ = function(_1ak/* s92g */, _1al/* s92h */){
  while(1){
    var _1am/* s92i */ = E(_1ak/* s92g */);
    if(!_1am/* s92i */._){
      return E(_1al/* s92h */);
    }else{
      _1ak/* s92g */ = _1am/* s92i */.b;
      _1al/* s92h */ = _1am/* s92i */.a;
      continue;
    }
  }
},
_1an/* ifiText1 */ = new T(function(){
  return B(_14G/* Control.Exception.Base.recSelError */("ifiText"));
}),
_1ao/* isChecked_f1 */ = new T(function(){
  return (function (jq) { return jq.prop('checked') === true; });
}),
_1ap/* isRadioSelected_f1 */ = new T(function(){
  return (function (jq) { return jq.length; });
}),
_1aq/* isRadioSelected1 */ = function(_1ar/* snWy */, _/* EXTERNAL */){
  var _1as/* snWJ */ = eval/* EXTERNAL */(E(_Ou/* FormEngine.JQuery.getRadioValue2 */)),
  _1at/* snWR */ = E(_1as/* snWJ */)(toJSStr/* EXTERNAL */(B(_12/* GHC.Base.++ */(_Ow/* FormEngine.JQuery.getRadioValue4 */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1ar/* snWy */, _Ov/* FormEngine.JQuery.getRadioValue3 */));
  },1))))),
  _1au/* snWX */ = E(_1ap/* FormEngine.JQuery.isRadioSelected_f1 */)(_1at/* snWR */);
  return new T(function(){
    var _1av/* snX1 */ = Number/* EXTERNAL */(_1au/* snWX */),
    _1aw/* snX5 */ = jsTrunc/* EXTERNAL */(_1av/* snX1 */);
    return _1aw/* snX5 */>0;
  });
},
_1ax/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */(": empty list"));
}),
_1ay/* errorEmptyList */ = function(_1az/* s9sr */){
  return new F(function(){return err/* EXTERNAL */(B(_12/* GHC.Base.++ */(_4W/* GHC.List.prel_list_str */, new T(function(){
    return B(_12/* GHC.Base.++ */(_1az/* s9sr */, _1ax/* GHC.List.lvl */));
  },1))));});
},
_1aA/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("last"));
}),
_1aB/* last1 */ = new T(function(){
  return B(_1ay/* GHC.List.errorEmptyList */(_1aA/* GHC.List.lvl16 */));
}),
_1aC/* lfiAvailableOptions1 */ = new T(function(){
  return B(_14G/* Control.Exception.Base.recSelError */("lfiAvailableOptions"));
}),
_1aD/* lvl12 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Submit"));
}),
_1aE/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("value"));
}),
_1aF/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'button\' class=\'submit\'>"));
}),
_1aG/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'labeltd more-space\' style=\'text-align: center\'>"));
}),
_1aH/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<table style=\'margin-top: 10px\'>"));
}),
_1aI/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Save"));
}),
_1aJ/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'submit\'>"));
}),
_1aK/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("MultipleGroupElement rendering not implemented yet"));
}),
_1aL/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-section\'>"));
}),
_1aM/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("\u25be"));
}),
_1aN/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1aO/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("checked"));
}),
_1aP/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("name"));
}),
_1aQ/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'checkbox\'>"));
}),
_1aR/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("level"));
}),
_1aS/* lvl27 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'optional-group\'>"));
}),
_1aT/* lvl28 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(">"));
}),
_1aU/* lvl29 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<h"));
}),
_1aV/* lvl30 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("framed"));
}),
_1aW/* lvl31 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'simple-group\'>"));
}),
_1aX/* lvl32 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("selected"));
}),
_1aY/* lvl33 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<option>"));
}),
_1aZ/* lvl34 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("identity"));
}),
_1b0/* lvl35 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<select>"));
}),
_1b1/* lvl36 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div>"));
}),
_1b2/* lvl37 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<br>"));
}),
_1b3/* lvl38 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'radio\'>"));
}),
_1b4/* lvl39 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div></div>"));
}),
_1b5/* lvl40 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<td class=\'more-space\' colspan=\'2\'>"));
}),
_1b6/* lvl41 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;&nbsp;"));
}),
_1b7/* lvl42 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("&nbsp;"));
}),
_1b8/* lvl43 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'number\'>"));
}),
_1b9/* lvl44 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'email\'>"));
}),
_1ba/* lvl45 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<textarea>"));
}),
_1bb/* lvl46 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<input type=\'text\'>"));
}),
_1bc/* lvl47 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("renderElement did not unify"));
}),
_1bd/* lvl48 */ = new T(function(){
  return B(_4a/* GHC.Show.$wshowSignedInt */(0, 0, _I/* GHC.Types.[] */));
}),
_1be/* onBlur2 */ = "(function (ev, jq) { jq.blur(ev); })",
_1bf/* onBlur1 */ = function(_1bg/* snGJ */, _1bh/* snGK */, _/* EXTERNAL */){
  var _1bi/* snGW */ = __createJSFunc/* EXTERNAL */(2, function(_1bj/* snGN */, _/* EXTERNAL */){
    var _1bk/* snGP */ = B(A2(E(_1bg/* snGJ */),_1bj/* snGN */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1bl/* snGZ */ = E(_1bh/* snGK */),
  _1bm/* snH4 */ = eval/* EXTERNAL */(E(_1be/* FormEngine.JQuery.onBlur2 */)),
  _1bn/* snHc */ = E(_1bm/* snH4 */)(_1bi/* snGW */, _1bl/* snGZ */);
  return _1bl/* snGZ */;
},
_1bo/* onChange2 */ = "(function (ev, jq) { jq.change(ev); })",
_1bp/* onChange1 */ = function(_1bq/* snF2 */, _1br/* snF3 */, _/* EXTERNAL */){
  var _1bs/* snFf */ = __createJSFunc/* EXTERNAL */(2, function(_1bt/* snF6 */, _/* EXTERNAL */){
    var _1bu/* snF8 */ = B(A2(E(_1bq/* snF2 */),_1bt/* snF6 */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1bv/* snFi */ = E(_1br/* snF3 */),
  _1bw/* snFn */ = eval/* EXTERNAL */(E(_1bo/* FormEngine.JQuery.onChange2 */)),
  _1bx/* snFv */ = E(_1bw/* snFn */)(_1bs/* snFf */, _1bv/* snFi */);
  return _1bv/* snFi */;
},
_1by/* onKeyup2 */ = "(function (ev, jq) { jq.keyup(ev); })",
_1bz/* onKeyup1 */ = function(_1bA/* snGa */, _1bB/* snGb */, _/* EXTERNAL */){
  var _1bC/* snGn */ = __createJSFunc/* EXTERNAL */(2, function(_1bD/* snGe */, _/* EXTERNAL */){
    var _1bE/* snGg */ = B(A2(E(_1bA/* snGa */),_1bD/* snGe */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1bF/* snGq */ = E(_1bB/* snGb */),
  _1bG/* snGv */ = eval/* EXTERNAL */(E(_1by/* FormEngine.JQuery.onKeyup2 */)),
  _1bH/* snGD */ = E(_1bG/* snGv */)(_1bC/* snGn */, _1bF/* snGq */);
  return _1bF/* snGq */;
},
_1bI/* optionElemValue */ = function(_1bJ/* s60j */){
  var _1bK/* s60k */ = E(_1bJ/* s60j */);
  if(!_1bK/* s60k */._){
    var _1bL/* s60n */ = E(_1bK/* s60k */.a);
    return (_1bL/* s60n */._==0) ? E(_1bL/* s60n */.a) : E(_1bL/* s60n */.b);
  }else{
    var _1bM/* s60v */ = E(_1bK/* s60k */.a);
    return (_1bM/* s60v */._==0) ? E(_1bM/* s60v */.a) : E(_1bM/* s60v */.b);
  }
},
_1bN/* optionSectionId1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_detail"));
}),
_1bO/* filter */ = function(_1bP/*  s9DD */, _1bQ/*  s9DE */){
  while(1){
    var _1bR/*  filter */ = B((function(_1bS/* s9DD */, _1bT/* s9DE */){
      var _1bU/* s9DF */ = E(_1bT/* s9DE */);
      if(!_1bU/* s9DF */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1bV/* s9DG */ = _1bU/* s9DF */.a,
        _1bW/* s9DH */ = _1bU/* s9DF */.b;
        if(!B(A1(_1bS/* s9DD */,_1bV/* s9DG */))){
          var _1bX/*   s9DD */ = _1bS/* s9DD */;
          _1bP/*  s9DD */ = _1bX/*   s9DD */;
          _1bQ/*  s9DE */ = _1bW/* s9DH */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1bV/* s9DG */,new T(function(){
            return B(_1bO/* GHC.List.filter */(_1bS/* s9DD */, _1bW/* s9DH */));
          }));
        }
      }
    })(_1bP/*  s9DD */, _1bQ/*  s9DE */));
    if(_1bR/*  filter */!=__continue/* EXTERNAL */){
      return _1bR/*  filter */;
    }
  }
},
_1bY/* $wlvl */ = function(_1bZ/* skCd */){
  var _1c0/* skCe */ = function(_1c1/* skCf */){
    var _1c2/* skCg */ = function(_1c3/* skCh */){
      if(_1bZ/* skCd */<48){
        switch(E(_1bZ/* skCd */)){
          case 45:
            return true;
          case 95:
            return true;
          default:
            return false;
        }
      }else{
        if(_1bZ/* skCd */>57){
          switch(E(_1bZ/* skCd */)){
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
    if(_1bZ/* skCd */<97){
      return new F(function(){return _1c2/* skCg */(_/* EXTERNAL */);});
    }else{
      if(_1bZ/* skCd */>122){
        return new F(function(){return _1c2/* skCg */(_/* EXTERNAL */);});
      }else{
        return true;
      }
    }
  };
  if(_1bZ/* skCd */<65){
    return new F(function(){return _1c0/* skCe */(_/* EXTERNAL */);});
  }else{
    if(_1bZ/* skCd */>90){
      return new F(function(){return _1c0/* skCe */(_/* EXTERNAL */);});
    }else{
      return true;
    }
  }
},
_1c4/* radioId1 */ = function(_1c5/* skCw */){
  return new F(function(){return _1bY/* FormEngine.FormElement.Identifiers.$wlvl */(E(_1c5/* skCw */));});
},
_1c6/* radioId2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("_"));
}),
_1c7/* radioId */ = function(_1c8/* skCz */, _1c9/* skCA */){
  var _1ca/* skD4 */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_1c6/* FormEngine.FormElement.Identifiers.radioId2 */, new T(function(){
      var _1cb/* skCN */ = E(_1c9/* skCA */);
      if(!_1cb/* skCN */._){
        var _1cc/* skCQ */ = E(_1cb/* skCN */.a);
        if(!_1cc/* skCQ */._){
          return B(_1bO/* GHC.List.filter */(_1c4/* FormEngine.FormElement.Identifiers.radioId1 */, _1cc/* skCQ */.a));
        }else{
          return B(_1bO/* GHC.List.filter */(_1c4/* FormEngine.FormElement.Identifiers.radioId1 */, _1cc/* skCQ */.b));
        }
      }else{
        var _1cd/* skCY */ = E(_1cb/* skCN */.a);
        if(!_1cd/* skCY */._){
          return B(_1bO/* GHC.List.filter */(_1c4/* FormEngine.FormElement.Identifiers.radioId1 */, _1cd/* skCY */.a));
        }else{
          return B(_1bO/* GHC.List.filter */(_1c4/* FormEngine.FormElement.Identifiers.radioId1 */, _1cd/* skCY */.b));
        }
      }
    },1)));
  },1);
  return new F(function(){return _12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_1c8/* skCz */)))).b)), _1ca/* skD4 */);});
},
_1ce/* target_f1 */ = new T(function(){
  return (function (js) {return $(js.target); });
}),
_1cf/* foldElements2 */ = function(_1cg/* s92v */, _1ch/* s92w */, _1ci/* s92x */, _1cj/* s92y */, _/* EXTERNAL */){
  var _1ck/* s92A */ = function(_1cl/* s92B */, _/* EXTERNAL */){
    return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cg/* s92v */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
  },
  _1cm/* s92D */ = E(_1cg/* s92v */);
  switch(_1cm/* s92D */._){
    case 0:
      return new F(function(){return _1ae/* FormEngine.JQuery.errorjq1 */(_1bc/* FormEngine.FormElement.Rendering.lvl47 */, _1cj/* s92y */, _/* EXTERNAL */);});
      break;
    case 1:
      var _1cn/* s93N */ = function(_/* EXTERNAL */){
        var _1co/* s92N */ = B(_7v/* FormEngine.JQuery.select1 */(_1bb/* FormEngine.FormElement.Rendering.lvl46 */, _/* EXTERNAL */)),
        _1cp/* s92Q */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1cm/* s92D */.a)),
        _1cq/* s933 */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1cp/* s92Q */.b)), E(_1co/* s92N */), _/* EXTERNAL */)),
        _1cr/* s936 */ = function(_/* EXTERNAL */, _1cs/* s938 */){
          var _1ct/* s939 */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1cm/* s92D */.b, _1cs/* s938 */, _/* EXTERNAL */)),
          _1cu/* s93f */ = B(_17X/* FormEngine.JQuery.onMouseEnter1 */(function(_1cv/* s93c */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1ct/* s939 */, _/* EXTERNAL */)),
          _1cw/* s93l */ = B(_1bz/* FormEngine.JQuery.onKeyup1 */(function(_1cx/* s93i */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cu/* s93f */, _/* EXTERNAL */)),
          _1cy/* s93r */ = B(_1bf/* FormEngine.JQuery.onBlur1 */(function(_1cz/* s93o */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cw/* s93l */, _/* EXTERNAL */));
          return new F(function(){return _18d/* FormEngine.JQuery.onMouseLeave1 */(function(_1cA/* s93u */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cy/* s93r */, _/* EXTERNAL */);});
        },
        _1cB/* s93x */ = E(_1cp/* s92Q */.c);
        if(!_1cB/* s93x */._){
          var _1cC/* s93A */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1cq/* s933 */), _/* EXTERNAL */));
          return new F(function(){return _1cr/* s936 */(_/* EXTERNAL */, E(_1cC/* s93A */));});
        }else{
          var _1cD/* s93I */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1cB/* s93x */.a, E(_1cq/* s933 */), _/* EXTERNAL */));
          return new F(function(){return _1cr/* s936 */(_/* EXTERNAL */, E(_1cD/* s93I */));});
        }
      };
      return new F(function(){return _19e/* FormEngine.FormElement.Rendering.$wa2 */(_1cn/* s93N */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */);});
      break;
    case 2:
      var _1cE/* s94U */ = function(_/* EXTERNAL */){
        var _1cF/* s93U */ = B(_7v/* FormEngine.JQuery.select1 */(_1ba/* FormEngine.FormElement.Rendering.lvl45 */, _/* EXTERNAL */)),
        _1cG/* s93X */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1cm/* s92D */.a)),
        _1cH/* s94a */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1cG/* s93X */.b)), E(_1cF/* s93U */), _/* EXTERNAL */)),
        _1cI/* s94d */ = function(_/* EXTERNAL */, _1cJ/* s94f */){
          var _1cK/* s94g */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1cm/* s92D */.b, _1cJ/* s94f */, _/* EXTERNAL */)),
          _1cL/* s94m */ = B(_17X/* FormEngine.JQuery.onMouseEnter1 */(function(_1cM/* s94j */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cK/* s94g */, _/* EXTERNAL */)),
          _1cN/* s94s */ = B(_1bz/* FormEngine.JQuery.onKeyup1 */(function(_1cO/* s94p */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cL/* s94m */, _/* EXTERNAL */)),
          _1cP/* s94y */ = B(_1bf/* FormEngine.JQuery.onBlur1 */(function(_1cQ/* s94v */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cN/* s94s */, _/* EXTERNAL */));
          return new F(function(){return _18d/* FormEngine.JQuery.onMouseLeave1 */(function(_1cR/* s94B */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1cP/* s94y */, _/* EXTERNAL */);});
        },
        _1cS/* s94E */ = E(_1cG/* s93X */.c);
        if(!_1cS/* s94E */._){
          var _1cT/* s94H */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1cH/* s94a */), _/* EXTERNAL */));
          return new F(function(){return _1cI/* s94d */(_/* EXTERNAL */, E(_1cT/* s94H */));});
        }else{
          var _1cU/* s94P */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1cS/* s94E */.a, E(_1cH/* s94a */), _/* EXTERNAL */));
          return new F(function(){return _1cI/* s94d */(_/* EXTERNAL */, E(_1cU/* s94P */));});
        }
      };
      return new F(function(){return _19e/* FormEngine.FormElement.Rendering.$wa2 */(_1cE/* s94U */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */);});
      break;
    case 3:
      var _1cV/* s961 */ = function(_/* EXTERNAL */){
        var _1cW/* s951 */ = B(_7v/* FormEngine.JQuery.select1 */(_1b9/* FormEngine.FormElement.Rendering.lvl44 */, _/* EXTERNAL */)),
        _1cX/* s954 */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1cm/* s92D */.a)),
        _1cY/* s95h */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1cX/* s954 */.b)), E(_1cW/* s951 */), _/* EXTERNAL */)),
        _1cZ/* s95k */ = function(_/* EXTERNAL */, _1d0/* s95m */){
          var _1d1/* s95n */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1cm/* s92D */.b, _1d0/* s95m */, _/* EXTERNAL */)),
          _1d2/* s95t */ = B(_17X/* FormEngine.JQuery.onMouseEnter1 */(function(_1d3/* s95q */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1d1/* s95n */, _/* EXTERNAL */)),
          _1d4/* s95z */ = B(_1bz/* FormEngine.JQuery.onKeyup1 */(function(_1d5/* s95w */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1d2/* s95t */, _/* EXTERNAL */)),
          _1d6/* s95F */ = B(_1bf/* FormEngine.JQuery.onBlur1 */(function(_1d7/* s95C */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1d4/* s95z */, _/* EXTERNAL */));
          return new F(function(){return _18d/* FormEngine.JQuery.onMouseLeave1 */(function(_1d8/* s95I */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1d6/* s95F */, _/* EXTERNAL */);});
        },
        _1d9/* s95L */ = E(_1cX/* s954 */.c);
        if(!_1d9/* s95L */._){
          var _1da/* s95O */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1cY/* s95h */), _/* EXTERNAL */));
          return new F(function(){return _1cZ/* s95k */(_/* EXTERNAL */, E(_1da/* s95O */));});
        }else{
          var _1db/* s95W */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1d9/* s95L */.a, E(_1cY/* s95h */), _/* EXTERNAL */));
          return new F(function(){return _1cZ/* s95k */(_/* EXTERNAL */, E(_1db/* s95W */));});
        }
      };
      return new F(function(){return _19e/* FormEngine.FormElement.Rendering.$wa2 */(_1cV/* s961 */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */);});
      break;
    case 4:
      var _1dc/* s962 */ = _1cm/* s92D */.a,
      _1dd/* s968 */ = function(_1de/* s969 */, _/* EXTERNAL */){
        return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
      },
      _1df/* s9bR */ = function(_/* EXTERNAL */){
        var _1dg/* s96c */ = B(_7v/* FormEngine.JQuery.select1 */(_1b8/* FormEngine.FormElement.Rendering.lvl43 */, _/* EXTERNAL */)),
        _1dh/* s96f */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1dc/* s962 */)),
        _1di/* s96h */ = _1dh/* s96f */.b,
        _1dj/* s96s */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1di/* s96h */)), E(_1dg/* s96c */), _/* EXTERNAL */)),
        _1dk/* s96y */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1di/* s96h */)), E(_1dj/* s96s */), _/* EXTERNAL */)),
        _1dl/* s96B */ = function(_/* EXTERNAL */, _1dm/* s96D */){
          var _1dn/* s96E */ = function(_/* EXTERNAL */, _1do/* s96G */){
            var _1dp/* s96K */ = B(_17X/* FormEngine.JQuery.onMouseEnter1 */(function(_1dq/* s96H */, _/* EXTERNAL */){
              return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
            }, _1do/* s96G */, _/* EXTERNAL */)),
            _1dr/* s96Q */ = B(_1bz/* FormEngine.JQuery.onKeyup1 */(function(_1ds/* s96N */, _/* EXTERNAL */){
              return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
            }, _1dp/* s96K */, _/* EXTERNAL */)),
            _1dt/* s96W */ = B(_1bf/* FormEngine.JQuery.onBlur1 */(function(_1du/* s96T */, _/* EXTERNAL */){
              return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
            }, _1dr/* s96Q */, _/* EXTERNAL */)),
            _1dv/* s972 */ = B(_18d/* FormEngine.JQuery.onMouseLeave1 */(function(_1dw/* s96Z */, _/* EXTERNAL */){
              return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
            }, _1dt/* s96W */, _/* EXTERNAL */)),
            _1dx/* s977 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b7/* FormEngine.FormElement.Rendering.lvl42 */, E(_1dv/* s972 */), _/* EXTERNAL */)),
            _1dy/* s97a */ = E(_1dc/* s962 */);
            if(_1dy/* s97a */._==3){
              var _1dz/* s97e */ = E(_1dy/* s97a */.b);
              switch(_1dz/* s97e */._){
                case 0:
                  return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1dz/* s97e */.a, _1dx/* s977 */, _/* EXTERNAL */);});
                  break;
                case 1:
                  var _1dA/* s97h */ = new T(function(){
                    return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1dy/* s97a */.a).b)), _OE/* FormEngine.FormItem.nfiUnitId1 */));
                  }),
                  _1dB/* s97t */ = E(_1dz/* s97e */.a);
                  if(!_1dB/* s97t */._){
                    return _1dx/* s977 */;
                  }else{
                    var _1dC/* s97u */ = _1dB/* s97t */.a,
                    _1dD/* s97v */ = _1dB/* s97t */.b,
                    _1dE/* s97y */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b3/* FormEngine.FormElement.Rendering.lvl38 */, E(_1dx/* s977 */), _/* EXTERNAL */)),
                    _1dF/* s97D */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1dC/* s97u */, E(_1dE/* s97y */), _/* EXTERNAL */)),
                    _1dG/* s97I */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, _1dA/* s97h */, E(_1dF/* s97D */), _/* EXTERNAL */)),
                    _1dH/* s97N */ = B(_186/* FormEngine.JQuery.$wa30 */(_1ck/* s92A */, E(_1dG/* s97I */), _/* EXTERNAL */)),
                    _1dI/* s97S */ = B(_17Q/* FormEngine.JQuery.$wa23 */(_1ck/* s92A */, E(_1dH/* s97N */), _/* EXTERNAL */)),
                    _1dJ/* s97X */ = B(_18m/* FormEngine.JQuery.$wa31 */(_1dd/* s968 */, E(_1dI/* s97S */), _/* EXTERNAL */)),
                    _1dK/* s980 */ = function(_/* EXTERNAL */, _1dL/* s982 */){
                      var _1dM/* s983 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, _1dL/* s982 */, _/* EXTERNAL */)),
                      _1dN/* s988 */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1dC/* s97u */, E(_1dM/* s983 */), _/* EXTERNAL */));
                      return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b6/* FormEngine.FormElement.Rendering.lvl41 */, _1dN/* s988 */, _/* EXTERNAL */);});
                    },
                    _1dO/* s98b */ = E(_1cm/* s92D */.c);
                    if(!_1dO/* s98b */._){
                      var _1dP/* s98e */ = B(_1dK/* s980 */(_/* EXTERNAL */, E(_1dJ/* s97X */))),
                      _1dQ/* s98h */ = function(_1dR/* s98i */, _1dS/* s98j */, _/* EXTERNAL */){
                        while(1){
                          var _1dT/* s98l */ = E(_1dR/* s98i */);
                          if(!_1dT/* s98l */._){
                            return _1dS/* s98j */;
                          }else{
                            var _1dU/* s98m */ = _1dT/* s98l */.a,
                            _1dV/* s98q */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b3/* FormEngine.FormElement.Rendering.lvl38 */, E(_1dS/* s98j */), _/* EXTERNAL */)),
                            _1dW/* s98v */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1dU/* s98m */, E(_1dV/* s98q */), _/* EXTERNAL */)),
                            _1dX/* s98A */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, _1dA/* s97h */, E(_1dW/* s98v */), _/* EXTERNAL */)),
                            _1dY/* s98F */ = B(_186/* FormEngine.JQuery.$wa30 */(_1ck/* s92A */, E(_1dX/* s98A */), _/* EXTERNAL */)),
                            _1dZ/* s98K */ = B(_17Q/* FormEngine.JQuery.$wa23 */(_1ck/* s92A */, E(_1dY/* s98F */), _/* EXTERNAL */)),
                            _1e0/* s98P */ = B(_18m/* FormEngine.JQuery.$wa31 */(_1dd/* s968 */, E(_1dZ/* s98K */), _/* EXTERNAL */)),
                            _1e1/* s98U */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, E(_1e0/* s98P */), _/* EXTERNAL */)),
                            _1e2/* s98Z */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1dU/* s98m */, E(_1e1/* s98U */), _/* EXTERNAL */)),
                            _1e3/* s994 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b6/* FormEngine.FormElement.Rendering.lvl41 */, E(_1e2/* s98Z */), _/* EXTERNAL */));
                            _1dR/* s98i */ = _1dT/* s98l */.b;
                            _1dS/* s98j */ = _1e3/* s994 */;
                            continue;
                          }
                        }
                      };
                      return new F(function(){return _1dQ/* s98h */(_1dD/* s97v */, _1dP/* s98e */, _/* EXTERNAL */);});
                    }else{
                      var _1e4/* s997 */ = _1dO/* s98b */.a;
                      if(!B(_Lg/* GHC.Base.eqString */(_1e4/* s997 */, _1dC/* s97u */))){
                        var _1e5/* s99b */ = B(_1dK/* s980 */(_/* EXTERNAL */, E(_1dJ/* s97X */))),
                        _1e6/* s99e */ = function(_1e7/*  s99f */, _1e8/*  s99g */, _/* EXTERNAL */){
                          while(1){
                            var _1e9/*  s99e */ = B((function(_1ea/* s99f */, _1eb/* s99g */, _/* EXTERNAL */){
                              var _1ec/* s99i */ = E(_1ea/* s99f */);
                              if(!_1ec/* s99i */._){
                                return _1eb/* s99g */;
                              }else{
                                var _1ed/* s99j */ = _1ec/* s99i */.a,
                                _1ee/* s99k */ = _1ec/* s99i */.b,
                                _1ef/* s99n */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b3/* FormEngine.FormElement.Rendering.lvl38 */, E(_1eb/* s99g */), _/* EXTERNAL */)),
                                _1eg/* s99s */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1ed/* s99j */, E(_1ef/* s99n */), _/* EXTERNAL */)),
                                _1eh/* s99x */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, _1dA/* s97h */, E(_1eg/* s99s */), _/* EXTERNAL */)),
                                _1ei/* s99C */ = B(_186/* FormEngine.JQuery.$wa30 */(_1ck/* s92A */, E(_1eh/* s99x */), _/* EXTERNAL */)),
                                _1ej/* s99H */ = B(_17Q/* FormEngine.JQuery.$wa23 */(_1ck/* s92A */, E(_1ei/* s99C */), _/* EXTERNAL */)),
                                _1ek/* s99M */ = B(_18m/* FormEngine.JQuery.$wa31 */(_1dd/* s968 */, E(_1ej/* s99H */), _/* EXTERNAL */)),
                                _1el/* s99P */ = function(_/* EXTERNAL */, _1em/* s99R */){
                                  var _1en/* s99S */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, _1em/* s99R */, _/* EXTERNAL */)),
                                  _1eo/* s99X */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1ed/* s99j */, E(_1en/* s99S */), _/* EXTERNAL */));
                                  return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b6/* FormEngine.FormElement.Rendering.lvl41 */, _1eo/* s99X */, _/* EXTERNAL */);});
                                };
                                if(!B(_Lg/* GHC.Base.eqString */(_1e4/* s997 */, _1ed/* s99j */))){
                                  var _1ep/* s9a3 */ = B(_1el/* s99P */(_/* EXTERNAL */, E(_1ek/* s99M */)));
                                  _1e7/*  s99f */ = _1ee/* s99k */;
                                  _1e8/*  s99g */ = _1ep/* s9a3 */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1eq/* s9a8 */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1ek/* s99M */), _/* EXTERNAL */)),
                                  _1er/* s9ad */ = B(_1el/* s99P */(_/* EXTERNAL */, E(_1eq/* s9a8 */)));
                                  _1e7/*  s99f */ = _1ee/* s99k */;
                                  _1e8/*  s99g */ = _1er/* s9ad */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1e7/*  s99f */, _1e8/*  s99g */, _/* EXTERNAL */));
                            if(_1e9/*  s99e */!=__continue/* EXTERNAL */){
                              return _1e9/*  s99e */;
                            }
                          }
                        };
                        return new F(function(){return _1e6/* s99e */(_1dD/* s97v */, _1e5/* s99b */, _/* EXTERNAL */);});
                      }else{
                        var _1es/* s9ai */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1dJ/* s97X */), _/* EXTERNAL */)),
                        _1et/* s9an */ = B(_1dK/* s980 */(_/* EXTERNAL */, E(_1es/* s9ai */))),
                        _1eu/* s9aq */ = function(_1ev/*  s9ar */, _1ew/*  s9as */, _/* EXTERNAL */){
                          while(1){
                            var _1ex/*  s9aq */ = B((function(_1ey/* s9ar */, _1ez/* s9as */, _/* EXTERNAL */){
                              var _1eA/* s9au */ = E(_1ey/* s9ar */);
                              if(!_1eA/* s9au */._){
                                return _1ez/* s9as */;
                              }else{
                                var _1eB/* s9av */ = _1eA/* s9au */.a,
                                _1eC/* s9aw */ = _1eA/* s9au */.b,
                                _1eD/* s9az */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b3/* FormEngine.FormElement.Rendering.lvl38 */, E(_1ez/* s9as */), _/* EXTERNAL */)),
                                _1eE/* s9aE */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1eB/* s9av */, E(_1eD/* s9az */), _/* EXTERNAL */)),
                                _1eF/* s9aJ */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, _1dA/* s97h */, E(_1eE/* s9aE */), _/* EXTERNAL */)),
                                _1eG/* s9aO */ = B(_186/* FormEngine.JQuery.$wa30 */(_1ck/* s92A */, E(_1eF/* s9aJ */), _/* EXTERNAL */)),
                                _1eH/* s9aT */ = B(_17Q/* FormEngine.JQuery.$wa23 */(_1ck/* s92A */, E(_1eG/* s9aO */), _/* EXTERNAL */)),
                                _1eI/* s9aY */ = B(_18m/* FormEngine.JQuery.$wa31 */(_1dd/* s968 */, E(_1eH/* s9aT */), _/* EXTERNAL */)),
                                _1eJ/* s9b1 */ = function(_/* EXTERNAL */, _1eK/* s9b3 */){
                                  var _1eL/* s9b4 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, _1eK/* s9b3 */, _/* EXTERNAL */)),
                                  _1eM/* s9b9 */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1eB/* s9av */, E(_1eL/* s9b4 */), _/* EXTERNAL */));
                                  return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b6/* FormEngine.FormElement.Rendering.lvl41 */, _1eM/* s9b9 */, _/* EXTERNAL */);});
                                };
                                if(!B(_Lg/* GHC.Base.eqString */(_1e4/* s997 */, _1eB/* s9av */))){
                                  var _1eN/* s9bf */ = B(_1eJ/* s9b1 */(_/* EXTERNAL */, E(_1eI/* s9aY */)));
                                  _1ev/*  s9ar */ = _1eC/* s9aw */;
                                  _1ew/*  s9as */ = _1eN/* s9bf */;
                                  return __continue/* EXTERNAL */;
                                }else{
                                  var _1eO/* s9bk */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1eI/* s9aY */), _/* EXTERNAL */)),
                                  _1eP/* s9bp */ = B(_1eJ/* s9b1 */(_/* EXTERNAL */, E(_1eO/* s9bk */)));
                                  _1ev/*  s9ar */ = _1eC/* s9aw */;
                                  _1ew/*  s9as */ = _1eP/* s9bp */;
                                  return __continue/* EXTERNAL */;
                                }
                              }
                            })(_1ev/*  s9ar */, _1ew/*  s9as */, _/* EXTERNAL */));
                            if(_1ex/*  s9aq */!=__continue/* EXTERNAL */){
                              return _1ex/*  s9aq */;
                            }
                          }
                        };
                        return new F(function(){return _1eu/* s9aq */(_1dD/* s97v */, _1et/* s9an */, _/* EXTERNAL */);});
                      }
                    }
                  }
                  break;
                default:
                  return _1dx/* s977 */;
              }
            }else{
              return E(_16T/* FormEngine.FormItem.nfiUnit1 */);
            }
          },
          _1eQ/* s9bs */ = E(_1cm/* s92D */.b);
          if(!_1eQ/* s9bs */._){
            var _1eR/* s9bt */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _I/* GHC.Types.[] */, _1dm/* s96D */, _/* EXTERNAL */));
            return new F(function(){return _1dn/* s96E */(_/* EXTERNAL */, _1eR/* s9bt */);});
          }else{
            var _1eS/* s9by */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, B(_4A/* GHC.Show.$fShowInt_$cshow */(_1eQ/* s9bs */.a)), _1dm/* s96D */, _/* EXTERNAL */));
            return new F(function(){return _1dn/* s96E */(_/* EXTERNAL */, _1eS/* s9by */);});
          }
        },
        _1eT/* s9bB */ = E(_1dh/* s96f */.c);
        if(!_1eT/* s9bB */._){
          var _1eU/* s9bE */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1dk/* s96y */), _/* EXTERNAL */));
          return new F(function(){return _1dl/* s96B */(_/* EXTERNAL */, E(_1eU/* s9bE */));});
        }else{
          var _1eV/* s9bM */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1eT/* s9bB */.a, E(_1dk/* s96y */), _/* EXTERNAL */));
          return new F(function(){return _1dl/* s96B */(_/* EXTERNAL */, E(_1eV/* s9bM */));});
        }
      };
      return new F(function(){return _19e/* FormEngine.FormElement.Rendering.$wa2 */(_1df/* s9bR */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */);});
      break;
    case 5:
      var _1eW/* s9bW */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_199/* FormEngine.FormElement.Rendering.lvl5 */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1eX/* s9c4 */ = B(_186/* FormEngine.JQuery.$wa30 */(function(_1eY/* s9c1 */, _/* EXTERNAL */){
        return new F(function(){return _18X/* FormEngine.FormElement.Rendering.a4 */(_1cm/* s92D */, _/* EXTERNAL */);});
      }, E(_1eW/* s9bW */), _/* EXTERNAL */)),
      _1eZ/* s9cc */ = B(_18m/* FormEngine.JQuery.$wa31 */(function(_1f0/* s9c9 */, _/* EXTERNAL */){
        return new F(function(){return _18N/* FormEngine.FormElement.Rendering.a3 */(_1cm/* s92D */, _/* EXTERNAL */);});
      }, E(_1eX/* s9c4 */), _/* EXTERNAL */)),
      _1f1/* s9ch */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
      _1f2/* s9ck */ = __app1/* EXTERNAL */(_1f1/* s9ch */, E(_1eZ/* s9cc */)),
      _1f3/* s9cn */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
      _1f4/* s9cq */ = __app1/* EXTERNAL */(_1f3/* s9cn */, _1f2/* s9ck */),
      _1f5/* s9ct */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19a/* FormEngine.FormElement.Rendering.lvl6 */, _1f4/* s9cq */, _/* EXTERNAL */)),
      _1f6/* s9cz */ = __app1/* EXTERNAL */(_1f1/* s9ch */, E(_1f5/* s9ct */)),
      _1f7/* s9cD */ = __app1/* EXTERNAL */(_1f3/* s9cn */, _1f6/* s9cz */),
      _1f8/* s9cG */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19b/* FormEngine.FormElement.Rendering.lvl7 */, _1f7/* s9cD */, _/* EXTERNAL */)),
      _1f9/* s9cM */ = __app1/* EXTERNAL */(_1f1/* s9ch */, E(_1f8/* s9cG */)),
      _1fa/* s9cQ */ = __app1/* EXTERNAL */(_1f3/* s9cn */, _1f9/* s9cM */),
      _1fb/* s9cT */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b5/* FormEngine.FormElement.Rendering.lvl40 */, _1fa/* s9cQ */, _/* EXTERNAL */)),
      _1fc/* s9d2 */ = B(_KD/* FormEngine.JQuery.$wa34 */(new T(function(){
        var _1fd/* s9cY */ = E(_1cm/* s92D */.a);
        if(_1fd/* s9cY */._==4){
          return E(_1fd/* s9cY */.b);
        }else{
          return E(_1an/* FormEngine.FormItem.ifiText1 */);
        }
      },1), E(_1fb/* s9cT */), _/* EXTERNAL */)),
      _1fe/* s9d7 */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
      _1ff/* s9da */ = __app1/* EXTERNAL */(_1fe/* s9d7 */, E(_1fc/* s9d2 */)),
      _1fg/* s9de */ = __app1/* EXTERNAL */(_1fe/* s9d7 */, _1ff/* s9da */),
      _1fh/* s9di */ = __app1/* EXTERNAL */(_1fe/* s9d7 */, _1fg/* s9de */);
      return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a1 */(_1cm/* s92D */, _1fh/* s9di */, _/* EXTERNAL */);});
      break;
    case 6:
      var _1fi/* s9dm */ = _1cm/* s92D */.a,
      _1fj/* s9dn */ = _1cm/* s92D */.b,
      _1fk/* s9dp */ = new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1fi/* s9dm */)).b));
      }),
      _1fl/* s9dC */ = new T(function(){
        var _1fm/* s9dN */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1fi/* s9dm */)).c);
        if(!_1fm/* s9dN */._){
          return __Z/* EXTERNAL */;
        }else{
          return E(_1fm/* s9dN */.a);
        }
      }),
      _1fn/* s9dP */ = function(_1fo/* s9dQ */, _/* EXTERNAL */){
        var _1fp/* s9dS */ = B(_1aq/* FormEngine.JQuery.isRadioSelected1 */(_1fk/* s9dp */, _/* EXTERNAL */));
        return new F(function(){return _15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1cm/* s92D */, _1ch/* s92w */, _1fp/* s9dS */, _/* EXTERNAL */);});
      },
      _1fq/* s9dV */ = new T(function(){
        return B(_1aj/* FormEngine.FormElement.Rendering.go */(_1fj/* s9dn */, _1aB/* GHC.List.last1 */));
      }),
      _1fr/* s9dW */ = function(_1fs/* s9dX */, _/* EXTERNAL */){
        return new F(function(){return _7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1aN/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
          return B(_12/* GHC.Base.++ */(B(_1c7/* FormEngine.FormElement.Identifiers.radioId */(_1cm/* s92D */, _1fs/* s9dX */)), _1bN/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
        },1))), _/* EXTERNAL */);});
      },
      _1ft/* s9e2 */ = function(_1fu/* s9e3 */, _/* EXTERNAL */){
        while(1){
          var _1fv/* s9e5 */ = E(_1fu/* s9e3 */);
          if(!_1fv/* s9e5 */._){
            return _I/* GHC.Types.[] */;
          }else{
            var _1fw/* s9e7 */ = _1fv/* s9e5 */.b,
            _1fx/* s9e8 */ = E(_1fv/* s9e5 */.a);
            if(!_1fx/* s9e8 */._){
              _1fu/* s9e3 */ = _1fw/* s9e7 */;
              continue;
            }else{
              var _1fy/* s9ee */ = B(_1fr/* s9dW */(_1fx/* s9e8 */, _/* EXTERNAL */)),
              _1fz/* s9eh */ = B(_1ft/* s9e2 */(_1fw/* s9e7 */, _/* EXTERNAL */));
              return new T2(1,_1fy/* s9ee */,_1fz/* s9eh */);
            }
          }
        }
      },
      _1fA/* s9gU */ = function(_/* EXTERNAL */){
        var _1fB/* s9em */ = B(_7v/* FormEngine.JQuery.select1 */(_1b4/* FormEngine.FormElement.Rendering.lvl39 */, _/* EXTERNAL */)),
        _1fC/* s9ep */ = function(_1fD/*  s9eq */, _1fE/*  s9er */, _/* EXTERNAL */){
          while(1){
            var _1fF/*  s9ep */ = B((function(_1fG/* s9eq */, _1fH/* s9er */, _/* EXTERNAL */){
              var _1fI/* s9et */ = E(_1fG/* s9eq */);
              if(!_1fI/* s9et */._){
                return _1fH/* s9er */;
              }else{
                var _1fJ/* s9eu */ = _1fI/* s9et */.a,
                _1fK/* s9ev */ = _1fI/* s9et */.b,
                _1fL/* s9ey */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b3/* FormEngine.FormElement.Rendering.lvl38 */, E(_1fH/* s9er */), _/* EXTERNAL */)),
                _1fM/* s9eE */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_1c7/* FormEngine.FormElement.Identifiers.radioId */(_1cm/* s92D */, _1fJ/* s9eu */));
                },1), E(_1fL/* s9ey */), _/* EXTERNAL */)),
                _1fN/* s9eJ */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, _1fk/* s9dp */, E(_1fM/* s9eE */), _/* EXTERNAL */)),
                _1fO/* s9eO */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1fl/* s9dC */, E(_1fN/* s9eJ */), _/* EXTERNAL */)),
                _1fP/* s9eU */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
                  return B(_1bI/* FormEngine.FormElement.FormElement.optionElemValue */(_1fJ/* s9eu */));
                },1), E(_1fO/* s9eO */), _/* EXTERNAL */)),
                _1fQ/* s9eX */ = function(_/* EXTERNAL */, _1fR/* s9eZ */){
                  var _1fS/* s9ft */ = B(_17Q/* FormEngine.JQuery.$wa23 */(function(_1fT/* s9f0 */, _/* EXTERNAL */){
                    var _1fU/* s9f2 */ = B(_1ft/* s9e2 */(_1fj/* s9dn */, _/* EXTERNAL */)),
                    _1fV/* s9f5 */ = B(_1a4/* FormEngine.FormElement.Rendering.a5 */(_1fU/* s9f2 */, _/* EXTERNAL */)),
                    _1fW/* s9f8 */ = E(_1fJ/* s9eu */);
                    if(!_1fW/* s9f8 */._){
                      var _1fX/* s9fb */ = B(_1aq/* FormEngine.JQuery.isRadioSelected1 */(_1fk/* s9dp */, _/* EXTERNAL */));
                      return new F(function(){return _15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1cm/* s92D */, _1ch/* s92w */, _1fX/* s9fb */, _/* EXTERNAL */);});
                    }else{
                      var _1fY/* s9fh */ = B(_1fr/* s9dW */(_1fW/* s9f8 */, _/* EXTERNAL */)),
                      _1fZ/* s9fm */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _Le/* FormEngine.JQuery.appearJq2 */, E(_1fY/* s9fh */), _/* EXTERNAL */)),
                      _1g0/* s9fp */ = B(_1aq/* FormEngine.JQuery.isRadioSelected1 */(_1fk/* s9dp */, _/* EXTERNAL */));
                      return new F(function(){return _15G/* FormEngine.FormElement.Updating.inputFieldUpdate2 */(_1cm/* s92D */, _1ch/* s92w */, _1g0/* s9fp */, _/* EXTERNAL */);});
                    }
                  }, _1fR/* s9eZ */, _/* EXTERNAL */)),
                  _1g1/* s9fy */ = B(_18m/* FormEngine.JQuery.$wa31 */(_1fn/* s9dP */, E(_1fS/* s9ft */), _/* EXTERNAL */)),
                  _1g2/* s9fD */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18B/* FormEngine.FormElement.Rendering.lvl1 */, E(_1g1/* s9fy */), _/* EXTERNAL */)),
                  _1g3/* s9fJ */ = B(_KD/* FormEngine.JQuery.$wa34 */(new T(function(){
                    return B(_1bI/* FormEngine.FormElement.FormElement.optionElemValue */(_1fJ/* s9eu */));
                  },1), E(_1g2/* s9fD */), _/* EXTERNAL */)),
                  _1g4/* s9fM */ = E(_1fJ/* s9eu */);
                  if(!_1g4/* s9fM */._){
                    var _1g5/* s9fN */ = _1g4/* s9fM */.a,
                    _1g6/* s9fR */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1g3/* s9fJ */), _/* EXTERNAL */)),
                    _1g7/* s9fU */ = E(_1fq/* s9dV */);
                    if(!_1g7/* s9fU */._){
                      if(!B(_NY/* FormEngine.FormItem.$fEqOption_$c== */(_1g5/* s9fN */, _1g7/* s9fU */.a))){
                        return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b2/* FormEngine.FormElement.Rendering.lvl37 */, _1g6/* s9fR */, _/* EXTERNAL */);});
                      }else{
                        return _1g6/* s9fR */;
                      }
                    }else{
                      if(!B(_NY/* FormEngine.FormItem.$fEqOption_$c== */(_1g5/* s9fN */, _1g7/* s9fU */.a))){
                        return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b2/* FormEngine.FormElement.Rendering.lvl37 */, _1g6/* s9fR */, _/* EXTERNAL */);});
                      }else{
                        return _1g6/* s9fR */;
                      }
                    }
                  }else{
                    var _1g8/* s9g2 */ = _1g4/* s9fM */.a,
                    _1g9/* s9g7 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aM/* FormEngine.FormElement.Rendering.lvl21 */, E(_1g3/* s9fJ */), _/* EXTERNAL */)),
                    _1ga/* s9ga */ = E(_1fq/* s9dV */);
                    if(!_1ga/* s9ga */._){
                      if(!B(_NY/* FormEngine.FormItem.$fEqOption_$c== */(_1g8/* s9g2 */, _1ga/* s9ga */.a))){
                        return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b2/* FormEngine.FormElement.Rendering.lvl37 */, _1g9/* s9g7 */, _/* EXTERNAL */);});
                      }else{
                        return _1g9/* s9g7 */;
                      }
                    }else{
                      if(!B(_NY/* FormEngine.FormItem.$fEqOption_$c== */(_1g8/* s9g2 */, _1ga/* s9ga */.a))){
                        return new F(function(){return _1a8/* FormEngine.JQuery.appendT1 */(_1b2/* FormEngine.FormElement.Rendering.lvl37 */, _1g9/* s9g7 */, _/* EXTERNAL */);});
                      }else{
                        return _1g9/* s9g7 */;
                      }
                    }
                  }
                },
                _1gb/* s9gi */ = E(_1fJ/* s9eu */);
                if(!_1gb/* s9gi */._){
                  if(!E(_1gb/* s9gi */.b)){
                    var _1gc/* s9go */ = B(_1fQ/* s9eX */(_/* EXTERNAL */, E(_1fP/* s9eU */)));
                    _1fD/*  s9eq */ = _1fK/* s9ev */;
                    _1fE/*  s9er */ = _1gc/* s9go */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1gd/* s9gt */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1fP/* s9eU */), _/* EXTERNAL */)),
                    _1ge/* s9gy */ = B(_1fQ/* s9eX */(_/* EXTERNAL */, E(_1gd/* s9gt */)));
                    _1fD/*  s9eq */ = _1fK/* s9ev */;
                    _1fE/*  s9er */ = _1ge/* s9gy */;
                    return __continue/* EXTERNAL */;
                  }
                }else{
                  if(!E(_1gb/* s9gi */.b)){
                    var _1gf/* s9gH */ = B(_1fQ/* s9eX */(_/* EXTERNAL */, E(_1fP/* s9eU */)));
                    _1fD/*  s9eq */ = _1fK/* s9ev */;
                    _1fE/*  s9er */ = _1gf/* s9gH */;
                    return __continue/* EXTERNAL */;
                  }else{
                    var _1gg/* s9gM */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1fP/* s9eU */), _/* EXTERNAL */)),
                    _1gh/* s9gR */ = B(_1fQ/* s9eX */(_/* EXTERNAL */, E(_1gg/* s9gM */)));
                    _1fD/*  s9eq */ = _1fK/* s9ev */;
                    _1fE/*  s9er */ = _1gh/* s9gR */;
                    return __continue/* EXTERNAL */;
                  }
                }
              }
            })(_1fD/*  s9eq */, _1fE/*  s9er */, _/* EXTERNAL */));
            if(_1fF/*  s9ep */!=__continue/* EXTERNAL */){
              return _1fF/*  s9ep */;
            }
          }
        };
        return new F(function(){return _1fC/* s9ep */(_1fj/* s9dn */, _1fB/* s9em */, _/* EXTERNAL */);});
      },
      _1gi/* s9gV */ = B(_19e/* FormEngine.FormElement.Rendering.$wa2 */(_1fA/* s9gU */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1gj/* s9gY */ = function(_1gk/* s9gZ */, _1gl/* s9h0 */, _/* EXTERNAL */){
        while(1){
          var _1gm/* s9h2 */ = E(_1gk/* s9gZ */);
          if(!_1gm/* s9h2 */._){
            return _1gl/* s9h0 */;
          }else{
            var _1gn/* s9h5 */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1gm/* s9h2 */.a, _1ch/* s92w */, _1ci/* s92x */, _1gl/* s9h0 */, _/* EXTERNAL */));
            _1gk/* s9gZ */ = _1gm/* s9h2 */.b;
            _1gl/* s9h0 */ = _1gn/* s9h5 */;
            continue;
          }
        }
      },
      _1go/* s9h8 */ = function(_1gp/*  s9h9 */, _1gq/*  s9ha */, _/* EXTERNAL */){
        while(1){
          var _1gr/*  s9h8 */ = B((function(_1gs/* s9h9 */, _1gt/* s9ha */, _/* EXTERNAL */){
            var _1gu/* s9hc */ = E(_1gs/* s9h9 */);
            if(!_1gu/* s9hc */._){
              return _1gt/* s9ha */;
            }else{
              var _1gv/* s9he */ = _1gu/* s9hc */.b,
              _1gw/* s9hf */ = E(_1gu/* s9hc */.a);
              if(!_1gw/* s9hf */._){
                var _1gx/*   s9ha */ = _1gt/* s9ha */;
                _1gp/*  s9h9 */ = _1gv/* s9he */;
                _1gq/*  s9ha */ = _1gx/*   s9ha */;
                return __continue/* EXTERNAL */;
              }else{
                var _1gy/* s9hn */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b1/* FormEngine.FormElement.Rendering.lvl36 */, E(_1gt/* s9ha */), _/* EXTERNAL */)),
                _1gz/* s9hu */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                  return B(_12/* GHC.Base.++ */(B(_1c7/* FormEngine.FormElement.Identifiers.radioId */(_1cm/* s92D */, _1gw/* s9hf */)), _1bN/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                },1), E(_1gy/* s9hn */), _/* EXTERNAL */)),
                _1gA/* s9hz */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
                _1gB/* s9hC */ = __app1/* EXTERNAL */(_1gA/* s9hz */, E(_1gz/* s9hu */)),
                _1gC/* s9hF */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
                _1gD/* s9hI */ = __app1/* EXTERNAL */(_1gC/* s9hF */, _1gB/* s9hC */),
                _1gE/* s9hL */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, _1gD/* s9hI */, _/* EXTERNAL */)),
                _1gF/* s9hO */ = B(_1gj/* s9gY */(_1gw/* s9hf */.c, _1gE/* s9hL */, _/* EXTERNAL */)),
                _1gG/* s9hT */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
                _1gH/* s9hW */ = __app1/* EXTERNAL */(_1gG/* s9hT */, E(_1gF/* s9hO */)),
                _1gI/* s9hZ */ = function(_1gJ/*  s9i0 */, _1gK/*  s9i1 */, _1gL/*  s8fZ */, _/* EXTERNAL */){
                  while(1){
                    var _1gM/*  s9hZ */ = B((function(_1gN/* s9i0 */, _1gO/* s9i1 */, _1gP/* s8fZ */, _/* EXTERNAL */){
                      var _1gQ/* s9i3 */ = E(_1gN/* s9i0 */);
                      if(!_1gQ/* s9i3 */._){
                        return _1gO/* s9i1 */;
                      }else{
                        var _1gR/* s9i6 */ = _1gQ/* s9i3 */.b,
                        _1gS/* s9i7 */ = E(_1gQ/* s9i3 */.a);
                        if(!_1gS/* s9i7 */._){
                          var _1gT/*   s9i1 */ = _1gO/* s9i1 */,
                          _1gU/*   s8fZ */ = _/* EXTERNAL */;
                          _1gJ/*  s9i0 */ = _1gR/* s9i6 */;
                          _1gK/*  s9i1 */ = _1gT/*   s9i1 */;
                          _1gL/*  s8fZ */ = _1gU/*   s8fZ */;
                          return __continue/* EXTERNAL */;
                        }else{
                          var _1gV/* s9id */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1b1/* FormEngine.FormElement.Rendering.lvl36 */, _1gO/* s9i1 */, _/* EXTERNAL */)),
                          _1gW/* s9ik */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                            return B(_12/* GHC.Base.++ */(B(_1c7/* FormEngine.FormElement.Identifiers.radioId */(_1cm/* s92D */, _1gS/* s9i7 */)), _1bN/* FormEngine.FormElement.Identifiers.optionSectionId1 */));
                          },1), E(_1gV/* s9id */), _/* EXTERNAL */)),
                          _1gX/* s9iq */ = __app1/* EXTERNAL */(_1gA/* s9hz */, E(_1gW/* s9ik */)),
                          _1gY/* s9iu */ = __app1/* EXTERNAL */(_1gC/* s9hF */, _1gX/* s9iq */),
                          _1gZ/* s9ix */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, _1gY/* s9iu */, _/* EXTERNAL */)),
                          _1h0/* s9iA */ = B(_1gj/* s9gY */(_1gS/* s9i7 */.c, _1gZ/* s9ix */, _/* EXTERNAL */)),
                          _1h1/* s9iG */ = __app1/* EXTERNAL */(_1gG/* s9hT */, E(_1h0/* s9iA */)),
                          _1gU/*   s8fZ */ = _/* EXTERNAL */;
                          _1gJ/*  s9i0 */ = _1gR/* s9i6 */;
                          _1gK/*  s9i1 */ = _1h1/* s9iG */;
                          _1gL/*  s8fZ */ = _1gU/*   s8fZ */;
                          return __continue/* EXTERNAL */;
                        }
                      }
                    })(_1gJ/*  s9i0 */, _1gK/*  s9i1 */, _1gL/*  s8fZ */, _/* EXTERNAL */));
                    if(_1gM/*  s9hZ */!=__continue/* EXTERNAL */){
                      return _1gM/*  s9hZ */;
                    }
                  }
                };
                return new F(function(){return _1gI/* s9hZ */(_1gv/* s9he */, _1gH/* s9hW */, _/* EXTERNAL */, _/* EXTERNAL */);});
              }
            }
          })(_1gp/*  s9h9 */, _1gq/*  s9ha */, _/* EXTERNAL */));
          if(_1gr/*  s9h8 */!=__continue/* EXTERNAL */){
            return _1gr/*  s9h8 */;
          }
        }
      };
      return new F(function(){return _1go/* s9h8 */(_1fj/* s9dn */, _1gi/* s9gV */, _/* EXTERNAL */);});
      break;
    case 7:
      var _1h2/* s9iJ */ = _1cm/* s92D */.a,
      _1h3/* s9lB */ = function(_/* EXTERNAL */){
        var _1h4/* s9iP */ = B(_7v/* FormEngine.JQuery.select1 */(_1b0/* FormEngine.FormElement.Rendering.lvl35 */, _/* EXTERNAL */)),
        _1h5/* s9iS */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1h2/* s9iJ */)),
        _1h6/* s9j5 */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, B(_4Q/* FormEngine.FormItem.numbering2text */(_1h5/* s9iS */.b)), E(_1h4/* s9iP */), _/* EXTERNAL */)),
        _1h7/* s9j8 */ = function(_/* EXTERNAL */, _1h8/* s9ja */){
          var _1h9/* s9je */ = B(_1bf/* FormEngine.JQuery.onBlur1 */(function(_1ha/* s9jb */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1h8/* s9ja */, _/* EXTERNAL */)),
          _1hb/* s9jk */ = B(_1bp/* FormEngine.JQuery.onChange1 */(function(_1hc/* s9jh */, _/* EXTERNAL */){
            return new F(function(){return _17B/* FormEngine.FormElement.Rendering.$wa1 */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1h9/* s9je */, _/* EXTERNAL */)),
          _1hd/* s9jq */ = B(_18d/* FormEngine.JQuery.onMouseLeave1 */(function(_1he/* s9jn */, _/* EXTERNAL */){
            return new F(function(){return _17t/* FormEngine.FormElement.Rendering.$wa */(_1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, _/* EXTERNAL */);});
          }, _1hb/* s9jk */, _/* EXTERNAL */)),
          _1hf/* s9jt */ = E(_1h2/* s9iJ */);
          if(_1hf/* s9jt */._==6){
            var _1hg/* s9jx */ = E(_1hf/* s9jt */.b);
            if(!_1hg/* s9jx */._){
              return _1hd/* s9jq */;
            }else{
              var _1hh/* s9jz */ = _1hg/* s9jx */.b,
              _1hi/* s9jA */ = E(_1hg/* s9jx */.a),
              _1hj/* s9jB */ = _1hi/* s9jA */.a,
              _1hk/* s9jF */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aY/* FormEngine.FormElement.Rendering.lvl33 */, E(_1hd/* s9jq */), _/* EXTERNAL */)),
              _1hl/* s9jK */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1hj/* s9jB */, E(_1hk/* s9jF */), _/* EXTERNAL */)),
              _1hm/* s9jP */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1hi/* s9jA */.b, E(_1hl/* s9jK */), _/* EXTERNAL */)),
              _1hn/* s9jS */ = E(_1cm/* s92D */.b);
              if(!_1hn/* s9jS */._){
                var _1ho/* s9jT */ = function(_1hp/* s9jU */, _1hq/* s9jV */, _/* EXTERNAL */){
                  while(1){
                    var _1hr/* s9jX */ = E(_1hp/* s9jU */);
                    if(!_1hr/* s9jX */._){
                      return _1hq/* s9jV */;
                    }else{
                      var _1hs/* s9k0 */ = E(_1hr/* s9jX */.a),
                      _1ht/* s9k5 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aY/* FormEngine.FormElement.Rendering.lvl33 */, E(_1hq/* s9jV */), _/* EXTERNAL */)),
                      _1hu/* s9ka */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1hs/* s9k0 */.a, E(_1ht/* s9k5 */), _/* EXTERNAL */)),
                      _1hv/* s9kf */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1hs/* s9k0 */.b, E(_1hu/* s9ka */), _/* EXTERNAL */));
                      _1hp/* s9jU */ = _1hr/* s9jX */.b;
                      _1hq/* s9jV */ = _1hv/* s9kf */;
                      continue;
                    }
                  }
                };
                return new F(function(){return _1ho/* s9jT */(_1hh/* s9jz */, _1hm/* s9jP */, _/* EXTERNAL */);});
              }else{
                var _1hw/* s9ki */ = _1hn/* s9jS */.a;
                if(!B(_Lg/* GHC.Base.eqString */(_1hj/* s9jB */, _1hw/* s9ki */))){
                  var _1hx/* s9kk */ = function(_1hy/* s9kl */, _1hz/* s9km */, _/* EXTERNAL */){
                    while(1){
                      var _1hA/* s9ko */ = E(_1hy/* s9kl */);
                      if(!_1hA/* s9ko */._){
                        return _1hz/* s9km */;
                      }else{
                        var _1hB/* s9kq */ = _1hA/* s9ko */.b,
                        _1hC/* s9kr */ = E(_1hA/* s9ko */.a),
                        _1hD/* s9ks */ = _1hC/* s9kr */.a,
                        _1hE/* s9kw */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aY/* FormEngine.FormElement.Rendering.lvl33 */, E(_1hz/* s9km */), _/* EXTERNAL */)),
                        _1hF/* s9kB */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1hD/* s9ks */, E(_1hE/* s9kw */), _/* EXTERNAL */)),
                        _1hG/* s9kG */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1hC/* s9kr */.b, E(_1hF/* s9kB */), _/* EXTERNAL */));
                        if(!B(_Lg/* GHC.Base.eqString */(_1hD/* s9ks */, _1hw/* s9ki */))){
                          _1hy/* s9kl */ = _1hB/* s9kq */;
                          _1hz/* s9km */ = _1hG/* s9kG */;
                          continue;
                        }else{
                          var _1hH/* s9kM */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aX/* FormEngine.FormElement.Rendering.lvl32 */, _1aX/* FormEngine.FormElement.Rendering.lvl32 */, E(_1hG/* s9kG */), _/* EXTERNAL */));
                          _1hy/* s9kl */ = _1hB/* s9kq */;
                          _1hz/* s9km */ = _1hH/* s9kM */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1hx/* s9kk */(_1hh/* s9jz */, _1hm/* s9jP */, _/* EXTERNAL */);});
                }else{
                  var _1hI/* s9kR */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aX/* FormEngine.FormElement.Rendering.lvl32 */, _1aX/* FormEngine.FormElement.Rendering.lvl32 */, E(_1hm/* s9jP */), _/* EXTERNAL */)),
                  _1hJ/* s9kU */ = function(_1hK/* s9kV */, _1hL/* s9kW */, _/* EXTERNAL */){
                    while(1){
                      var _1hM/* s9kY */ = E(_1hK/* s9kV */);
                      if(!_1hM/* s9kY */._){
                        return _1hL/* s9kW */;
                      }else{
                        var _1hN/* s9l0 */ = _1hM/* s9kY */.b,
                        _1hO/* s9l1 */ = E(_1hM/* s9kY */.a),
                        _1hP/* s9l2 */ = _1hO/* s9l1 */.a,
                        _1hQ/* s9l6 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aY/* FormEngine.FormElement.Rendering.lvl33 */, E(_1hL/* s9kW */), _/* EXTERNAL */)),
                        _1hR/* s9lb */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, _1hP/* s9l2 */, E(_1hQ/* s9l6 */), _/* EXTERNAL */)),
                        _1hS/* s9lg */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1hO/* s9l1 */.b, E(_1hR/* s9lb */), _/* EXTERNAL */));
                        if(!B(_Lg/* GHC.Base.eqString */(_1hP/* s9l2 */, _1hw/* s9ki */))){
                          _1hK/* s9kV */ = _1hN/* s9l0 */;
                          _1hL/* s9kW */ = _1hS/* s9lg */;
                          continue;
                        }else{
                          var _1hT/* s9lm */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aX/* FormEngine.FormElement.Rendering.lvl32 */, _1aX/* FormEngine.FormElement.Rendering.lvl32 */, E(_1hS/* s9lg */), _/* EXTERNAL */));
                          _1hK/* s9kV */ = _1hN/* s9l0 */;
                          _1hL/* s9kW */ = _1hT/* s9lm */;
                          continue;
                        }
                      }
                    }
                  };
                  return new F(function(){return _1hJ/* s9kU */(_1hh/* s9jz */, _1hI/* s9kR */, _/* EXTERNAL */);});
                }
              }
            }
          }else{
            return E(_1aC/* FormEngine.FormItem.lfiAvailableOptions1 */);
          }
        },
        _1hU/* s9lp */ = E(_1h5/* s9iS */.c);
        if(!_1hU/* s9lp */._){
          var _1hV/* s9ls */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _I/* GHC.Types.[] */, E(_1h6/* s9j5 */), _/* EXTERNAL */));
          return new F(function(){return _1h7/* s9j8 */(_/* EXTERNAL */, _1hV/* s9ls */);});
        }else{
          var _1hW/* s9ly */ = B(_Kb/* FormEngine.JQuery.$wa6 */(_1aZ/* FormEngine.FormElement.Rendering.lvl34 */, _1hU/* s9lp */.a, E(_1h6/* s9j5 */), _/* EXTERNAL */));
          return new F(function(){return _1h7/* s9j8 */(_/* EXTERNAL */, _1hW/* s9ly */);});
        }
      };
      return new F(function(){return _19e/* FormEngine.FormElement.Rendering.$wa2 */(_1h3/* s9lB */, _1cm/* s92D */, _1ch/* s92w */, _1ci/* s92x */, E(_1cj/* s92y */), _/* EXTERNAL */);});
      break;
    case 8:
      var _1hX/* s9lC */ = _1cm/* s92D */.a,
      _1hY/* s9lD */ = _1cm/* s92D */.b,
      _1hZ/* s9lH */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aW/* FormEngine.FormElement.Rendering.lvl31 */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1i0/* s9lM */ = new T(function(){
        var _1i1/* s9lN */ = E(_1hX/* s9lC */);
        switch(_1i1/* s9lN */._){
          case 8:
            return E(_1i1/* s9lN */.b);
            break;
          case 9:
            return E(_1i1/* s9lN */.b);
            break;
          case 10:
            return E(_1i1/* s9lN */.b);
            break;
          default:
            return E(_8o/* FormEngine.FormItem.$fShowNumbering2 */);
        }
      }),
      _1i2/* s9lY */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aR/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        return B(_4A/* GHC.Show.$fShowInt_$cshow */(_1i0/* s9lM */));
      },1), E(_1hZ/* s9lH */), _/* EXTERNAL */)),
      _1i3/* s9m1 */ = E(_1i0/* s9lM */),
      _1i4/* s9m3 */ = function(_/* EXTERNAL */, _1i5/* s9m5 */){
        var _1i6/* s9m9 */ = __app1/* EXTERNAL */(E(_Ki/* FormEngine.JQuery.addClassInside_f3 */), _1i5/* s9m5 */),
        _1i7/* s9mf */ = __app1/* EXTERNAL */(E(_Kh/* FormEngine.JQuery.addClassInside_f2 */), _1i6/* s9m9 */),
        _1i8/* s9mi */ = B(_4f/* FormEngine.FormItem.fiDescriptor */(_1hX/* s9lC */)),
        _1i9/* s9mn */ = _1i8/* s9mi */.e,
        _1ia/* s9ms */ = E(_1i8/* s9mi */.a);
        if(!_1ia/* s9ms */._){
          var _1ib/* s9mt */ = function(_/* EXTERNAL */, _1ic/* s9mv */){
            var _1id/* s9mw */ = function(_1ie/* s9mx */, _1if/* s9my */, _/* EXTERNAL */){
              while(1){
                var _1ig/* s9mA */ = E(_1ie/* s9mx */);
                if(!_1ig/* s9mA */._){
                  return _1if/* s9my */;
                }else{
                  var _1ih/* s9mD */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1ig/* s9mA */.a, _1ch/* s92w */, _1ci/* s92x */, _1if/* s9my */, _/* EXTERNAL */));
                  _1ie/* s9mx */ = _1ig/* s9mA */.b;
                  _1if/* s9my */ = _1ih/* s9mD */;
                  continue;
                }
              }
            },
            _1ii/* s9mG */ = B(_1id/* s9mw */(_1hY/* s9lD */, _1ic/* s9mv */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_Kg/* FormEngine.JQuery.addClassInside_f1 */), E(_1ii/* s9mG */));});
          },
          _1ij/* s9mS */ = E(_1i9/* s9mn */);
          if(!_1ij/* s9mS */._){
            return new F(function(){return _1ib/* s9mt */(_/* EXTERNAL */, _1i7/* s9mf */);});
          }else{
            var _1ik/* s9mV */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18s/* FormEngine.FormElement.Rendering.lvl */, _1i7/* s9mf */, _/* EXTERNAL */)),
            _1il/* s9n0 */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1ij/* s9mS */.a, E(_1ik/* s9mV */), _/* EXTERNAL */));
            return new F(function(){return _1ib/* s9mt */(_/* EXTERNAL */, _1il/* s9n0 */);});
          }
        }else{
          var _1im/* s9n7 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(B(_12/* GHC.Base.++ */(_1aU/* FormEngine.FormElement.Rendering.lvl29 */, new T(function(){
            return B(_12/* GHC.Base.++ */(B(_4a/* GHC.Show.$wshowSignedInt */(0, _1i3/* s9m1 */, _I/* GHC.Types.[] */)), _1aT/* FormEngine.FormElement.Rendering.lvl28 */));
          },1))), _1i7/* s9mf */, _/* EXTERNAL */)),
          _1in/* s9nc */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1ia/* s9ms */.a, E(_1im/* s9n7 */), _/* EXTERNAL */)),
          _1io/* s9nf */ = function(_/* EXTERNAL */, _1ip/* s9nh */){
            var _1iq/* s9ni */ = function(_1ir/* s9nj */, _1is/* s9nk */, _/* EXTERNAL */){
              while(1){
                var _1it/* s9nm */ = E(_1ir/* s9nj */);
                if(!_1it/* s9nm */._){
                  return _1is/* s9nk */;
                }else{
                  var _1iu/* s9np */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1it/* s9nm */.a, _1ch/* s92w */, _1ci/* s92x */, _1is/* s9nk */, _/* EXTERNAL */));
                  _1ir/* s9nj */ = _1it/* s9nm */.b;
                  _1is/* s9nk */ = _1iu/* s9np */;
                  continue;
                }
              }
            },
            _1iv/* s9ns */ = B(_1iq/* s9ni */(_1hY/* s9lD */, _1ip/* s9nh */, _/* EXTERNAL */));
            return new F(function(){return __app1/* EXTERNAL */(E(_Kg/* FormEngine.JQuery.addClassInside_f1 */), E(_1iv/* s9ns */));});
          },
          _1iw/* s9nE */ = E(_1i9/* s9mn */);
          if(!_1iw/* s9nE */._){
            return new F(function(){return _1io/* s9nf */(_/* EXTERNAL */, _1in/* s9nc */);});
          }else{
            var _1ix/* s9nI */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18s/* FormEngine.FormElement.Rendering.lvl */, E(_1in/* s9nc */), _/* EXTERNAL */)),
            _1iy/* s9nN */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1iw/* s9nE */.a, E(_1ix/* s9nI */), _/* EXTERNAL */));
            return new F(function(){return _1io/* s9nf */(_/* EXTERNAL */, _1iy/* s9nN */);});
          }
        }
      };
      if(_1i3/* s9m1 */<=1){
        return new F(function(){return _1i4/* s9m3 */(_/* EXTERNAL */, E(_1i2/* s9lY */));});
      }else{
        var _1iz/* s9nW */ = B(_17J/* FormEngine.JQuery.$wa1 */(_1aV/* FormEngine.FormElement.Rendering.lvl30 */, E(_1i2/* s9lY */), _/* EXTERNAL */));
        return new F(function(){return _1i4/* s9m3 */(_/* EXTERNAL */, E(_1iz/* s9nW */));});
      }
      break;
    case 9:
      var _1iA/* s9o1 */ = _1cm/* s92D */.a,
      _1iB/* s9o3 */ = _1cm/* s92D */.c,
      _1iC/* s9o7 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aS/* FormEngine.FormElement.Rendering.lvl27 */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1iD/* s9ot */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aR/* FormEngine.FormElement.Rendering.lvl26 */, new T(function(){
        var _1iE/* s9oc */ = E(_1iA/* s9o1 */);
        switch(_1iE/* s9oc */._){
          case 8:
            return B(_4a/* GHC.Show.$wshowSignedInt */(0, E(_1iE/* s9oc */.b), _I/* GHC.Types.[] */));
            break;
          case 9:
            return B(_4a/* GHC.Show.$wshowSignedInt */(0, E(_1iE/* s9oc */.b), _I/* GHC.Types.[] */));
            break;
          case 10:
            return B(_4a/* GHC.Show.$wshowSignedInt */(0, E(_1iE/* s9oc */.b), _I/* GHC.Types.[] */));
            break;
          default:
            return E(_1bd/* FormEngine.FormElement.Rendering.lvl48 */);
        }
      },1), E(_1iC/* s9o7 */), _/* EXTERNAL */)),
      _1iF/* s9oB */ = B(_186/* FormEngine.JQuery.$wa30 */(function(_1iG/* s9oy */, _/* EXTERNAL */){
        return new F(function(){return _18X/* FormEngine.FormElement.Rendering.a4 */(_1cm/* s92D */, _/* EXTERNAL */);});
      }, E(_1iD/* s9ot */), _/* EXTERNAL */)),
      _1iH/* s9oJ */ = B(_18m/* FormEngine.JQuery.$wa31 */(function(_1iI/* s9oG */, _/* EXTERNAL */){
        return new F(function(){return _18N/* FormEngine.FormElement.Rendering.a3 */(_1cm/* s92D */, _/* EXTERNAL */);});
      }, E(_1iF/* s9oB */), _/* EXTERNAL */)),
      _1iJ/* s9oO */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
      _1iK/* s9oR */ = __app1/* EXTERNAL */(_1iJ/* s9oO */, E(_1iH/* s9oJ */)),
      _1iL/* s9oU */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
      _1iM/* s9oX */ = __app1/* EXTERNAL */(_1iL/* s9oU */, _1iK/* s9oR */),
      _1iN/* s9p0 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aQ/* FormEngine.FormElement.Rendering.lvl25 */, _1iM/* s9oX */, _/* EXTERNAL */)),
      _1iO/* s9pg */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aP/* FormEngine.FormElement.Rendering.lvl24 */, new T(function(){
        return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1iA/* s9o1 */)).b));
      },1), E(_1iN/* s9p0 */), _/* EXTERNAL */)),
      _1iP/* s9pj */ = function(_/* EXTERNAL */, _1iQ/* s9pl */){
        var _1iR/* s9pm */ = new T(function(){
          return B(_12/* GHC.Base.++ */(_1aN/* FormEngine.FormElement.Rendering.lvl22 */, new T(function(){
            return B(_1ac/* FormEngine.FormElement.Identifiers.checkboxId */(_1cm/* s92D */));
          },1)));
        }),
        _1iS/* s9pT */ = B(_17Q/* FormEngine.JQuery.$wa23 */(function(_1iT/* s9po */, _/* EXTERNAL */){
          var _1iU/* s9pq */ = B(_7v/* FormEngine.JQuery.select1 */(_1iR/* s9pm */, _/* EXTERNAL */)),
          _1iV/* s9py */ = __app1/* EXTERNAL */(E(_1ce/* FormEngine.JQuery.target_f1 */), E(_1iT/* s9po */)),
          _1iW/* s9pE */ = __app1/* EXTERNAL */(E(_1ao/* FormEngine.JQuery.isChecked_f1 */), _1iV/* s9py */);
          if(!_1iW/* s9pE */){
            var _1iX/* s9pK */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _LM/* FormEngine.JQuery.disappearJq2 */, E(_1iU/* s9pq */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }else{
            var _1iY/* s9pP */ = B(_77/* FormEngine.JQuery.$wa2 */(_Lf/* FormEngine.JQuery.appearJq3 */, _Le/* FormEngine.JQuery.appearJq2 */, E(_1iU/* s9pq */), _/* EXTERNAL */));
            return _0/* GHC.Tuple.() */;
          }
        }, _1iQ/* s9pl */, _/* EXTERNAL */)),
        _1iZ/* s9pW */ = B(_18E/* FormEngine.FormElement.Rendering.a2 */(_1cm/* s92D */, _1iS/* s9pT */, _/* EXTERNAL */)),
        _1j0/* s9pZ */ = function(_/* EXTERNAL */, _1j1/* s9q1 */){
          var _1j2/* s9qc */ = function(_/* EXTERNAL */, _1j3/* s9qe */){
            var _1j4/* s9qf */ = E(_1iB/* s9o3 */);
            if(!_1j4/* s9qf */._){
              return new F(function(){return __app1/* EXTERNAL */(E(_Kg/* FormEngine.JQuery.addClassInside_f1 */), _1j3/* s9qe */);});
            }else{
              var _1j5/* s9qp */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aL/* FormEngine.FormElement.Rendering.lvl20 */, _1j3/* s9qe */, _/* EXTERNAL */)),
              _1j6/* s9qv */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_198/* FormEngine.FormElement.Rendering.lvl11 */, new T(function(){
                return B(_1ac/* FormEngine.FormElement.Identifiers.checkboxId */(_1cm/* s92D */));
              },1), E(_1j5/* s9qp */), _/* EXTERNAL */)),
              _1j7/* s9qB */ = __app1/* EXTERNAL */(_1iJ/* s9oO */, E(_1j6/* s9qv */)),
              _1j8/* s9qF */ = __app1/* EXTERNAL */(_1iL/* s9oU */, _1j7/* s9qB */),
              _1j9/* s9qJ */ = function(_1ja/* s9qR */, _1jb/* s9qS */, _/* EXTERNAL */){
                while(1){
                  var _1jc/* s9qU */ = E(_1ja/* s9qR */);
                  if(!_1jc/* s9qU */._){
                    return _1jb/* s9qS */;
                  }else{
                    var _1jd/* s9qX */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1jc/* s9qU */.a, _1ch/* s92w */, _1ci/* s92x */, _1jb/* s9qS */, _/* EXTERNAL */));
                    _1ja/* s9qR */ = _1jc/* s9qU */.b;
                    _1jb/* s9qS */ = _1jd/* s9qX */;
                    continue;
                  }
                }
              },
              _1je/* s9r1 */ = B((function(_1jf/* s9qK */, _1jg/* s9qL */, _1jh/* s9qM */, _/* EXTERNAL */){
                var _1ji/* s9qO */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1jf/* s9qK */, _1ch/* s92w */, _1ci/* s92x */, _1jh/* s9qM */, _/* EXTERNAL */));
                return new F(function(){return _1j9/* s9qJ */(_1jg/* s9qL */, _1ji/* s9qO */, _/* EXTERNAL */);});
              })(_1j4/* s9qf */.a, _1j4/* s9qf */.b, _1j8/* s9qF */, _/* EXTERNAL */)),
              _1jj/* s9r6 */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
              _1jk/* s9r9 */ = __app1/* EXTERNAL */(_1jj/* s9r6 */, E(_1je/* s9r1 */));
              return new F(function(){return __app1/* EXTERNAL */(_1jj/* s9r6 */, _1jk/* s9r9 */);});
            }
          },
          _1jl/* s9rh */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1iA/* s9o1 */)).e);
          if(!_1jl/* s9rh */._){
            return new F(function(){return _1j2/* s9qc */(_/* EXTERNAL */, _1j1/* s9q1 */);});
          }else{
            var _1jm/* s9rj */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_18s/* FormEngine.FormElement.Rendering.lvl */, _1j1/* s9q1 */, _/* EXTERNAL */)),
            _1jn/* s9ro */ = B(_KD/* FormEngine.JQuery.$wa34 */(_1jl/* s9rh */.a, E(_1jm/* s9rj */), _/* EXTERNAL */));
            return new F(function(){return _1j2/* s9qc */(_/* EXTERNAL */, E(_1jn/* s9ro */));});
          }
        };
        if(!E(_1iB/* s9o3 */)._){
          var _1jo/* s9rw */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_I/* GHC.Types.[] */, E(_1iZ/* s9pW */), _/* EXTERNAL */));
          return new F(function(){return _1j0/* s9pZ */(_/* EXTERNAL */, E(_1jo/* s9rw */));});
        }else{
          var _1jp/* s9rF */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aM/* FormEngine.FormElement.Rendering.lvl21 */, E(_1iZ/* s9pW */), _/* EXTERNAL */));
          return new F(function(){return _1j0/* s9pZ */(_/* EXTERNAL */, E(_1jp/* s9rF */));});
        }
      };
      if(!E(_1cm/* s92D */.b)){
        return new F(function(){return _1iP/* s9pj */(_/* EXTERNAL */, E(_1iO/* s9pg */));});
      }else{
        var _1jq/* s9rP */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aO/* FormEngine.FormElement.Rendering.lvl23 */, _1aO/* FormEngine.FormElement.Rendering.lvl23 */, E(_1iO/* s9pg */), _/* EXTERNAL */));
        return new F(function(){return _1iP/* s9pj */(_/* EXTERNAL */, E(_1jq/* s9rP */));});
      }
      break;
    case 10:
      return new F(function(){return _1ae/* FormEngine.JQuery.errorjq1 */(_1aK/* FormEngine.FormElement.Rendering.lvl19 */, _1cj/* s92y */, _/* EXTERNAL */);});
      break;
    case 11:
      var _1jr/* s9s1 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aH/* FormEngine.FormElement.Rendering.lvl16 */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1js/* s9s6 */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
      _1jt/* s9s9 */ = __app1/* EXTERNAL */(_1js/* s9s6 */, E(_1jr/* s9s1 */)),
      _1ju/* s9sc */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
      _1jv/* s9sf */ = __app1/* EXTERNAL */(_1ju/* s9sc */, _1jt/* s9s9 */),
      _1jw/* s9si */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19a/* FormEngine.FormElement.Rendering.lvl6 */, _1jv/* s9sf */, _/* EXTERNAL */)),
      _1jx/* s9so */ = __app1/* EXTERNAL */(_1js/* s9s6 */, E(_1jw/* s9si */)),
      _1jy/* s9ss */ = __app1/* EXTERNAL */(_1ju/* s9sc */, _1jx/* s9so */),
      _1jz/* s9sv */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19b/* FormEngine.FormElement.Rendering.lvl7 */, _1jy/* s9ss */, _/* EXTERNAL */)),
      _1jA/* s9sB */ = __app1/* EXTERNAL */(_1js/* s9s6 */, E(_1jz/* s9sv */)),
      _1jB/* s9sF */ = __app1/* EXTERNAL */(_1ju/* s9sc */, _1jA/* s9sB */),
      _1jC/* s9sI */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl15 */, _1jB/* s9sF */, _/* EXTERNAL */)),
      _1jD/* s9sO */ = __app1/* EXTERNAL */(_1js/* s9s6 */, E(_1jC/* s9sI */)),
      _1jE/* s9sS */ = __app1/* EXTERNAL */(_1ju/* s9sc */, _1jD/* s9sO */),
      _1jF/* s9sV */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aJ/* FormEngine.FormElement.Rendering.lvl18 */, _1jE/* s9sS */, _/* EXTERNAL */)),
      _1jG/* s9td */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _1jH/* s9ta */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1cm/* s92D */.a)).a);
        if(!_1jH/* s9ta */._){
          return E(_1aI/* FormEngine.FormElement.Rendering.lvl17 */);
        }else{
          return E(_1jH/* s9ta */.a);
        }
      },1), E(_1jF/* s9sV */), _/* EXTERNAL */)),
      _1jI/* s9ti */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
      _1jJ/* s9tl */ = __app1/* EXTERNAL */(_1jI/* s9ti */, E(_1jG/* s9td */)),
      _1jK/* s9tp */ = __app1/* EXTERNAL */(_1jI/* s9ti */, _1jJ/* s9tl */),
      _1jL/* s9tt */ = __app1/* EXTERNAL */(_1jI/* s9ti */, _1jK/* s9tp */),
      _1jM/* s9tx */ = __app1/* EXTERNAL */(_1jI/* s9ti */, _1jL/* s9tt */);
      return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a1 */(_1cm/* s92D */, _1jM/* s9tx */, _/* EXTERNAL */);});
      break;
    default:
      var _1jN/* s9tF */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aH/* FormEngine.FormElement.Rendering.lvl16 */, E(_1cj/* s92y */), _/* EXTERNAL */)),
      _1jO/* s9tK */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
      _1jP/* s9tN */ = __app1/* EXTERNAL */(_1jO/* s9tK */, E(_1jN/* s9tF */)),
      _1jQ/* s9tQ */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
      _1jR/* s9tT */ = __app1/* EXTERNAL */(_1jQ/* s9tQ */, _1jP/* s9tN */),
      _1jS/* s9tW */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19a/* FormEngine.FormElement.Rendering.lvl6 */, _1jR/* s9tT */, _/* EXTERNAL */)),
      _1jT/* s9u2 */ = __app1/* EXTERNAL */(_1jO/* s9tK */, E(_1jS/* s9tW */)),
      _1jU/* s9u6 */ = __app1/* EXTERNAL */(_1jQ/* s9tQ */, _1jT/* s9u2 */),
      _1jV/* s9u9 */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_19b/* FormEngine.FormElement.Rendering.lvl7 */, _1jU/* s9u6 */, _/* EXTERNAL */)),
      _1jW/* s9uf */ = __app1/* EXTERNAL */(_1jO/* s9tK */, E(_1jV/* s9u9 */)),
      _1jX/* s9uj */ = __app1/* EXTERNAL */(_1jQ/* s9tQ */, _1jW/* s9uf */),
      _1jY/* s9um */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aG/* FormEngine.FormElement.Rendering.lvl15 */, _1jX/* s9uj */, _/* EXTERNAL */)),
      _1jZ/* s9us */ = __app1/* EXTERNAL */(_1jO/* s9tK */, E(_1jY/* s9um */)),
      _1k0/* s9uw */ = __app1/* EXTERNAL */(_1jQ/* s9tQ */, _1jZ/* s9us */),
      _1k1/* s9uz */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1aF/* FormEngine.FormElement.Rendering.lvl14 */, _1k0/* s9uw */, _/* EXTERNAL */)),
      _1k2/* s9uR */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1aE/* FormEngine.FormElement.Rendering.lvl13 */, new T(function(){
        var _1k3/* s9uO */ = E(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1cm/* s92D */.a)).a);
        if(!_1k3/* s9uO */._){
          return E(_1aD/* FormEngine.FormElement.Rendering.lvl12 */);
        }else{
          return E(_1k3/* s9uO */.a);
        }
      },1), E(_1k1/* s9uz */), _/* EXTERNAL */)),
      _1k4/* s9uW */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
      _1k5/* s9uZ */ = __app1/* EXTERNAL */(_1k4/* s9uW */, E(_1k2/* s9uR */)),
      _1k6/* s9v3 */ = __app1/* EXTERNAL */(_1k4/* s9uW */, _1k5/* s9uZ */),
      _1k7/* s9v7 */ = __app1/* EXTERNAL */(_1k4/* s9uW */, _1k6/* s9v3 */),
      _1k8/* s9vb */ = __app1/* EXTERNAL */(_1k4/* s9uW */, _1k7/* s9v7 */);
      return new F(function(){return _18w/* FormEngine.FormElement.Rendering.a1 */(_1cm/* s92D */, _1k8/* s9vb */, _/* EXTERNAL */);});
  }
},
_1k9/* foldElements1 */ = function(_1ka/* s9vf */, _1kb/* s9vg */, _1kc/* s9vh */, _1kd/* s9vi */, _/* EXTERNAL */){
  var _1ke/* s9vk */ = function(_1kf/* s9vl */, _1kg/* s9vm */, _/* EXTERNAL */){
    while(1){
      var _1kh/* s9vo */ = E(_1kf/* s9vl */);
      if(!_1kh/* s9vo */._){
        return _1kg/* s9vm */;
      }else{
        var _1ki/* s9vr */ = B(_1cf/* FormEngine.FormElement.Rendering.foldElements2 */(_1kh/* s9vo */.a, _1kb/* s9vg */, _1kc/* s9vh */, _1kg/* s9vm */, _/* EXTERNAL */));
        _1kf/* s9vl */ = _1kh/* s9vo */.b;
        _1kg/* s9vm */ = _1ki/* s9vr */;
        continue;
      }
    }
  };
  return new F(function(){return _1ke/* s9vk */(_1ka/* s9vf */, _1kd/* s9vi */, _/* EXTERNAL */);});
},
_1kj/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("textarea"));
}),
_1kk/* lvl1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("select"));
}),
_1kl/* selectSVG2 */ = "(function (selector, jq) { if (jq[0].contentDocument !== null) { var res = $(selector, jq[0].contentDocument.documentElement); if (res.length === 0) { console.warn(\'empty $ selection \' + selector); }; return res; } else return jq; })",
_1km/* $wa19 */ = function(_1kn/* snZB */, _1ko/* snZC */, _/* EXTERNAL */){
  var _1kp/* snZM */ = eval/* EXTERNAL */(E(_1kl/* FormEngine.JQuery.selectSVG2 */));
  return new F(function(){return E(_1kp/* snZM */)(toJSStr/* EXTERNAL */(E(_1kn/* snZB */)), _1ko/* snZC */);});
},
_1kq/* highlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#FBB48F"));
}),
_1kr/* tinkerDiagSvgConsumer6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("fill"));
}),
_1ks/* tinkerDiagSvgConsumer7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#"));
}),
_1kt/* tinkerDiagSvgConsumer5 */ = function(_1ku/* s4LM */, _1kv/* s4LN */, _/* EXTERNAL */){
  var _1kw/* s4LQ */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_1ks/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1kv/* s4LN */)), _/* EXTERNAL */)),
  _1kx/* s4LW */ = B(_1km/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1ks/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1ku/* s4LM */)), E(_1kw/* s4LQ */), _/* EXTERNAL */)),
  _1ky/* s4M1 */ = B(_77/* FormEngine.JQuery.$wa2 */(_1kr/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1kq/* DiagramDecorator.highlightCol */, E(_1kx/* s4LW */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1kz/* $wa */ = function(_1kA/* s4NK */, _/* EXTERNAL */){
  var _1kB/* s4NX */ = new T(function(){
    return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1kA/* s4NK */));
  }),
  _1kC/* s4NY */ = function(_1kD/* s4NZ */, _/* EXTERNAL */){
    while(1){
      var _1kE/* s4O1 */ = E(_1kD/* s4NZ */);
      if(!_1kE/* s4O1 */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1kF/* s4O4 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1kE/* s4O1 */.a, _1kB/* s4NX */, _/* EXTERNAL */));
        _1kD/* s4NZ */ = _1kE/* s4O1 */.b;
        continue;
      }
    }
  },
  _1kG/* s4O7 */ = B(_1kC/* s4NY */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_1kA/* s4NK */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1kH/* tinkerDiagramForElement1 */ = function(_1kI/* s4Oa */, _1kJ/* s4Ob */, _/* EXTERNAL */){
  return new F(function(){return _1kz/* DiagramDecorator.$wa */(_1kI/* s4Oa */, _/* EXTERNAL */);});
},
_1kK/* lvl10 */ = new T1(1,_1kH/* DiagramDecorator.tinkerDiagramForElement1 */),
_1kL/* lowlightCol */ = new T(function(){
  return B(unCStr/* EXTERNAL */("white"));
}),
_1kM/* $wa1 */ = function(_1kN/* s4L7 */, _/* EXTERNAL */){
  var _1kO/* s4Lk */ = new T(function(){
    return B(_12/* GHC.Base.++ */(_1ks/* DiagramDecorator.tinkerDiagSvgConsumer7 */, new T(function(){
      return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1kN/* s4L7 */));
    },1)));
  }),
  _1kP/* s4Lm */ = function(_1kQ/* s4Ln */, _/* EXTERNAL */){
    while(1){
      var _1kR/* s4Lp */ = E(_1kQ/* s4Ln */);
      if(!_1kR/* s4Lp */._){
        return _0/* GHC.Tuple.() */;
      }else{
        var _1kS/* s4Ls */ = B(_7v/* FormEngine.JQuery.select1 */(_1kO/* s4Lk */, _/* EXTERNAL */)),
        _1kT/* s4Ly */ = B(_1km/* FormEngine.JQuery.$wa19 */(B(_12/* GHC.Base.++ */(_1ks/* DiagramDecorator.tinkerDiagSvgConsumer7 */, _1kR/* s4Lp */.a)), E(_1kS/* s4Ls */), _/* EXTERNAL */)),
        _1kU/* s4LD */ = B(_77/* FormEngine.JQuery.$wa2 */(_1kr/* DiagramDecorator.tinkerDiagSvgConsumer6 */, _1kL/* DiagramDecorator.lowlightCol */, E(_1kT/* s4Ly */), _/* EXTERNAL */));
        _1kQ/* s4Ln */ = _1kR/* s4Lp */.b;
        continue;
      }
    }
  },
  _1kV/* s4LG */ = B(_1kP/* s4Lm */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_1kN/* s4L7 */)))).d, _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1kW/* tinkerDiagramForElementBlur1 */ = function(_1kX/* s4LJ */, _1kY/* s4LK */, _/* EXTERNAL */){
  return new F(function(){return _1kM/* DiagramDecorator.$wa1 */(_1kX/* s4LJ */, _/* EXTERNAL */);});
},
_1kZ/* lvl11 */ = new T1(1,_1kW/* DiagramDecorator.tinkerDiagramForElementBlur1 */),
_1l0/* lvl12 */ = new T3(0,_1kK/* Form.lvl10 */,_1kZ/* Form.lvl11 */,_2o/* GHC.Base.Nothing */),
_1l1/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'desc-subpane\'>"));
}),
_1l2/* lvl14 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("id"));
}),
_1l3/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<object class=\'svg-help\' href=\'http://caniuse.com/#feat=svg\' data=\'/static/img/data_process.svg\' type=\'image/svg+xml\'><br>"));
}),
_1l4/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<p class=\'long-desc\'>"));
}),
_1l5/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/hint-icon.png\' style=\'margin-right: 5px;\'>"));
}),
_1l6/* baseURL */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/"));
}),
_1l7/* staticURL1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("static/"));
}),
_1l8/* staticURL */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1l6/* Config.Config.baseURL */, _1l7/* Config.Config.staticURL1 */));
}),
_1l9/* lvl18 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1l8/* Config.Config.staticURL */, _1l5/* Form.lvl17 */));
}),
_1la/* lvl19 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img src=\'", _1l9/* Form.lvl18 */));
}),
_1lb/* lvl2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'main-pane\'></div>"));
}),
_1lc/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<span/>"));
}),
_1ld/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#m_questionnaire_form"));
}),
_1le/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input"));
}),
_1lf/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("input:checked"));
}),
_1lg/* lvl3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("<div class=\'form-subpane\'>"));
}),
_1lh/* lvl4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/valid.png\'/>"));
}),
_1li/* lvl5 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1l8/* Config.Config.staticURL */, _1lh/* Form.lvl4 */));
}),
_1lj/* lvl6 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1li/* Form.lvl5 */));
}),
_1lk/* lvl7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("/img/invalid.png\'/>"));
}),
_1ll/* lvl8 */ = new T(function(){
  return B(_12/* GHC.Base.++ */(_1l8/* Config.Config.staticURL */, _1lk/* Form.lvl7 */));
}),
_1lm/* lvl9 */ = new T(function(){
  return B(unAppCStr/* EXTERNAL */("<img class=\'validity-flag\' src=\'", _1ll/* Form.lvl8 */));
}),
_1ln/* click1 */ = function(_1lo/* snIJ */, _/* EXTERNAL */){
  return new F(function(){return _ND/* FormEngine.JQuery.$wa5 */(E(_1lo/* snIJ */), _/* EXTERNAL */);});
},
_1lp/* selectTab1 */ = function(_1lq/* slYk */, _1lr/* slYl */, _/* EXTERNAL */){
  var _1ls/* slYq */ = new T(function(){
    return B(_L9/* FormEngine.FormElement.Identifiers.tabId */(new T(function(){
      return B(_57/* GHC.List.$w!! */(_1lr/* slYl */, E(_1lq/* slYk */)));
    },1)));
  },1),
  _1lt/* slYs */ = B(_7v/* FormEngine.JQuery.select1 */(B(_12/* GHC.Base.++ */(_Lv/* FormEngine.FormElement.Tabs.colorizeTabs4 */, _1ls/* slYq */)), _/* EXTERNAL */));
  return new F(function(){return _1ln/* FormEngine.JQuery.click1 */(_1lt/* slYs */, _/* EXTERNAL */);});
},
_1lu/* tinkerDiagSvgConsumer4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_3"));
}),
_1lv/* tinkerDiagSvgCurator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_6"));
}),
_1lw/* tinkerDiagSvgCurator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_e"));
}),
_1lx/* tinkerDiagSvgCurator5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_5_i"));
}),
_1ly/* tinkerDiagSvgCurator6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_1"));
}),
_1lz/* tinkerDiagSvgCurator8 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_2"));
}),
_1lA/* tinkerDiagSvgInvestigator4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("institution_box"));
}),
_1lB/* tinkerDiagSvgManager4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_1"));
}),
_1lC/* tinkerDiagramForChapterElement1 */ = function(_1lD/* s4Od */, _/* EXTERNAL */){
  var _1lE/* s4Oq */ = B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(B(_7j/* FormEngine.FormElement.FormElement.formItem */(_1lD/* s4Od */)))).b));
  if(!_1lE/* s4Oq */._){
    return _0/* GHC.Tuple.() */;
  }else{
    var _1lF/* s4Os */ = _1lE/* s4Oq */.b;
    switch(E(_1lE/* s4Oq */.a)){
      case 48:
        if(!E(_1lF/* s4Os */)._){
          var _1lG/* s4Oy */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lA/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 49:
        if(!E(_1lF/* s4Os */)._){
          var _1lH/* s4OF */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lB/* DiagramDecorator.tinkerDiagSvgManager4 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 50:
        if(!E(_1lF/* s4Os */)._){
          var _1lI/* s4OM */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 51:
        if(!E(_1lF/* s4Os */)._){
          var _1lJ/* s4OT */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lu/* DiagramDecorator.tinkerDiagSvgConsumer4 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 52:
        if(!E(_1lF/* s4Os */)._){
          var _1lK/* s4P0 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 53:
        if(!E(_1lF/* s4Os */)._){
          var _1lL/* s4P6 */ = new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          }),
          _1lM/* s4P7 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lx/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1lL/* s4P6 */, _/* EXTERNAL */)),
          _1lN/* s4Pa */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lw/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1lL/* s4P6 */, _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 54:
        if(!E(_1lF/* s4Os */)._){
          var _1lO/* s4Ph */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lv/* DiagramDecorator.tinkerDiagSvgCurator3 */, new T(function(){
            return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lD/* s4Od */));
          },1), _/* EXTERNAL */));
          return _0/* GHC.Tuple.() */;
        }else{
          return _0/* GHC.Tuple.() */;
        }
        break;
      case 55:
        var _1lP/* s4Pm */ = E(_1lF/* s4Os */);
        return _0/* GHC.Tuple.() */;
      default:
        return _0/* GHC.Tuple.() */;
    }
  }
},
_1lQ/* generateQuestionnaire1 */ = function(_1lR/* sdDU */, _/* EXTERNAL */){
  var _1lS/* sdDW */ = B(_7v/* FormEngine.JQuery.select1 */(_1ld/* Form.lvl21 */, _/* EXTERNAL */)),
  _1lT/* sdE1 */ = new T2(1,_NP/* Form.aboutTab */,_1lR/* sdDU */),
  _1lU/* sdFT */ = new T(function(){
    var _1lV/* sdFS */ = function(_1lW/* sdE3 */, _/* EXTERNAL */){
      var _1lX/* sdE5 */ = B(_7v/* FormEngine.JQuery.select1 */(_1lb/* Form.lvl2 */, _/* EXTERNAL */)),
      _1lY/* sdEa */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1lg/* Form.lvl3 */, E(_1lX/* sdE5 */), _/* EXTERNAL */)),
      _1lZ/* sdEf */ = E(_Ki/* FormEngine.JQuery.addClassInside_f3 */),
      _1m0/* sdEi */ = __app1/* EXTERNAL */(_1lZ/* sdEf */, E(_1lY/* sdEa */)),
      _1m1/* sdEl */ = E(_Kh/* FormEngine.JQuery.addClassInside_f2 */),
      _1m2/* sdEo */ = __app1/* EXTERNAL */(_1m1/* sdEl */, _1m0/* sdEi */),
      _1m3/* sdEt */ = B(_1k9/* FormEngine.FormElement.Rendering.foldElements1 */(B(_K2/* FormEngine.FormElement.FormElement.$fHasChildrenFormElement_$cchildren */(_1lW/* sdE3 */)), new T3(0,_1lR/* sdDU */,_1lj/* Form.lvl6 */,_1lm/* Form.lvl9 */), _1l0/* Form.lvl12 */, _1m2/* sdEo */, _/* EXTERNAL */)),
      _1m4/* sdEy */ = E(_Kg/* FormEngine.JQuery.addClassInside_f1 */),
      _1m5/* sdEB */ = __app1/* EXTERNAL */(_1m4/* sdEy */, E(_1m3/* sdEt */)),
      _1m6/* sdEE */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1l1/* Form.lvl13 */, _1m5/* sdEB */, _/* EXTERNAL */)),
      _1m7/* sdEK */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1l2/* Form.lvl14 */, new T(function(){
        return B(_7m/* FormEngine.FormElement.Identifiers.descSubpaneId */(_1lW/* sdE3 */));
      },1), E(_1m6/* sdEE */), _/* EXTERNAL */)),
      _1m8/* sdEQ */ = __app1/* EXTERNAL */(_1lZ/* sdEf */, E(_1m7/* sdEK */)),
      _1m9/* sdEU */ = __app1/* EXTERNAL */(_1m1/* sdEl */, _1m8/* sdEQ */),
      _1ma/* sdEX */ = B(_Ni/* FormEngine.JQuery.$wa26 */(_1l3/* Form.lvl15 */, _1m9/* sdEU */, _/* EXTERNAL */)),
      _1mb/* sdF3 */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1l2/* Form.lvl14 */, new T(function(){
        return B(_NW/* FormEngine.FormElement.Identifiers.diagramId */(_1lW/* sdE3 */));
      },1), E(_1ma/* sdEX */), _/* EXTERNAL */)),
      _1mc/* sdFb */ = B(_Nw/* FormEngine.JQuery.$wa29 */(function(_1md/* sdF8 */, _/* EXTERNAL */){
        return new F(function(){return _1lC/* DiagramDecorator.tinkerDiagramForChapterElement1 */(_1lW/* sdE3 */, _/* EXTERNAL */);});
      }, E(_1mb/* sdF3 */), _/* EXTERNAL */)),
      _1me/* sdFg */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1l4/* Form.lvl16 */, E(_1mc/* sdFb */), _/* EXTERNAL */)),
      _1mf/* sdFm */ = B(_Kj/* FormEngine.JQuery.$wa20 */(_1l2/* Form.lvl14 */, new T(function(){
        return B(_NT/* FormEngine.FormElement.Identifiers.descSubpaneParagraphId */(_1lW/* sdE3 */));
      },1), E(_1me/* sdFg */), _/* EXTERNAL */)),
      _1mg/* sdFs */ = __app1/* EXTERNAL */(_1lZ/* sdEf */, E(_1mf/* sdFm */)),
      _1mh/* sdFw */ = __app1/* EXTERNAL */(_1m1/* sdEl */, _1mg/* sdFs */),
      _1mi/* sdFz */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1la/* Form.lvl19 */, _1mh/* sdFw */, _/* EXTERNAL */)),
      _1mj/* sdFE */ = B(_Ky/* FormEngine.JQuery.$wa3 */(_1lc/* Form.lvl20 */, E(_1mi/* sdFz */), _/* EXTERNAL */)),
      _1mk/* sdFK */ = __app1/* EXTERNAL */(_1m4/* sdEy */, E(_1mj/* sdFE */));
      return new F(function(){return __app1/* EXTERNAL */(_1m4/* sdEy */, _1mk/* sdFK */);});
    };
    return B(_2S/* GHC.Base.map */(_1lV/* sdFS */, _1lR/* sdDU */));
  }),
  _1ml/* sdFV */ = B(_M4/* FormEngine.FormElement.Tabs.$wa */(_1lT/* sdE1 */, new T2(1,_NR/* Form.aboutTabPaneJq1 */,_1lU/* sdFT */), E(_1lS/* sdDW */), _/* EXTERNAL */)),
  _1mm/* sdFY */ = B(_1lp/* FormEngine.FormElement.Tabs.selectTab1 */(_NH/* Form.aboutTab4 */, _1lT/* sdE1 */, _/* EXTERNAL */)),
  _1mn/* sdG1 */ = B(_7v/* FormEngine.JQuery.select1 */(_1lf/* Form.lvl23 */, _/* EXTERNAL */)),
  _1mo/* sdG6 */ = B(_ND/* FormEngine.JQuery.$wa5 */(E(_1mn/* sdG1 */), _/* EXTERNAL */)),
  _1mp/* sdGb */ = B(_ND/* FormEngine.JQuery.$wa5 */(E(_1mo/* sdG6 */), _/* EXTERNAL */)),
  _1mq/* sdGe */ = B(_7v/* FormEngine.JQuery.select1 */(_1le/* Form.lvl22 */, _/* EXTERNAL */)),
  _1mr/* sdGj */ = B(_Nd/* FormEngine.JQuery.$wa14 */(E(_1mq/* sdGe */), _/* EXTERNAL */)),
  _1ms/* sdGm */ = B(_7v/* FormEngine.JQuery.select1 */(_1kj/* Form.lvl */, _/* EXTERNAL */)),
  _1mt/* sdGr */ = B(_Nd/* FormEngine.JQuery.$wa14 */(E(_1ms/* sdGm */), _/* EXTERNAL */)),
  _1mu/* sdGu */ = B(_7v/* FormEngine.JQuery.select1 */(_1kk/* Form.lvl1 */, _/* EXTERNAL */)),
  _1mv/* sdGz */ = B(_Nd/* FormEngine.JQuery.$wa14 */(E(_1mu/* sdGu */), _/* EXTERNAL */));
  return _0/* GHC.Tuple.() */;
},
_1mw/* go */ = function(_1mx/* sieI */){
  while(1){
    var _1my/* sieJ */ = E(_1mx/* sieI */);
    if(!_1my/* sieJ */._){
      return false;
    }else{
      if(!E(_1my/* sieJ */.a)._){
        return true;
      }else{
        _1mx/* sieI */ = _1my/* sieJ */.b;
        continue;
      }
    }
  }
},
_1mz/* lvl */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Generate"));
}),
_1mA/* a2 */ = function(_1mB/* s1vnB */, _1mC/* s1vnC */){
  return new F(function(){return _1mD/* GHC.Read.$wa20 */(_1mC/* s1vnC */);});
},
_1mD/* $wa20 */ = function(_1mE/* s1vnD */){
  var _1mF/* s1vnI */ = new T(function(){
    return B(_11m/* Text.Read.Lex.expect2 */(function(_1mG/* s1vnF */){
      var _1mH/* s1vnG */ = E(_1mG/* s1vnF */);
      if(!_1mH/* s1vnG */._){
        return new F(function(){return A1(_1mE/* s1vnD */,_1mH/* s1vnG */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1mI/* s1vnJ */ = function(_1mJ/* s1vnK */){
    return E(_1mF/* s1vnI */);
  };
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1mK/* s1vnL */){
    return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1mK/* s1vnL */, _1mI/* s1vnJ */);});
  }), new T(function(){
    return new T1(1,B(_11U/* GHC.Read.$wa3 */(_1mA/* GHC.Read.a2 */, _1mE/* s1vnD */)));
  }));});
},
_1mL/* $fReadChar2 */ = function(_1mM/* s1vnR */, _1mN/* s1vnS */){
  return new F(function(){return _1mD/* GHC.Read.$wa20 */(_1mN/* s1vnS */);});
},
_1mO/* lvl6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("["));
}),
_1mP/* $wa */ = function(_1mQ/* s1vjF */, _1mR/* s1vjG */){
  var _1mS/* s1vjH */ = function(_1mT/* s1vjI */, _1mU/* s1vjJ */){
    var _1mV/* s1vjK */ = new T(function(){
      return B(A1(_1mU/* s1vjJ */,_I/* GHC.Types.[] */));
    }),
    _1mW/* s1vjL */ = new T(function(){
      var _1mX/* s1vjQ */ = function(_1mY/* s1vjM */){
        return new F(function(){return _1mS/* s1vjH */(_aC/* GHC.Types.True */, function(_1mZ/* s1vjN */){
          return new F(function(){return A1(_1mU/* s1vjJ */,new T2(1,_1mY/* s1vjM */,_1mZ/* s1vjN */));});
        });});
      };
      return B(A2(_1mQ/* s1vjF */,_11T/* Text.ParserCombinators.ReadPrec.minPrec */, _1mX/* s1vjQ */));
    }),
    _1n0/* s1vk8 */ = new T(function(){
      return B(_11m/* Text.Read.Lex.expect2 */(function(_1n1/* s1vjS */){
        var _1n2/* s1vjT */ = E(_1n1/* s1vjS */);
        if(_1n2/* s1vjT */._==2){
          var _1n3/* s1vjV */ = E(_1n2/* s1vjT */.a);
          if(!_1n3/* s1vjV */._){
            return new T0(2);
          }else{
            var _1n4/* s1vjX */ = _1n3/* s1vjV */.b;
            switch(E(_1n3/* s1vjV */.a)){
              case 44:
                return (E(_1n4/* s1vjX */)._==0) ? (!E(_1mT/* s1vjI */)) ? new T0(2) : E(_1mW/* s1vjL */) : new T0(2);
              case 93:
                return (E(_1n4/* s1vjX */)._==0) ? E(_1mV/* s1vjK */) : new T0(2);
              default:
                return new T0(2);
            }
          }
        }else{
          return new T0(2);
        }
      }));
    }),
    _1n5/* s1vk9 */ = function(_1n6/* s1vka */){
      return E(_1n0/* s1vk8 */);
    };
    return new T1(1,function(_1n7/* s1vkb */){
      return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1n7/* s1vkb */, _1n5/* s1vk9 */);});
    });
  },
  _1n8/* s1vkd */ = function(_1n9/* s1vkf */, _1na/* s1vkg */){
    return new F(function(){return _1nb/* s1vke */(_1na/* s1vkg */);});
  },
  _1nb/* s1vke */ = function(_1nc/* s1vkh */){
    var _1nd/* s1vki */ = new T(function(){
      var _1ne/* s1vkj */ = new T(function(){
        var _1nf/* s1vkq */ = new T(function(){
          var _1ng/* s1vkp */ = function(_1nh/* s1vkl */){
            return new F(function(){return _1mS/* s1vjH */(_aC/* GHC.Types.True */, function(_1ni/* s1vkm */){
              return new F(function(){return A1(_1nc/* s1vkh */,new T2(1,_1nh/* s1vkl */,_1ni/* s1vkm */));});
            });});
          };
          return B(A2(_1mQ/* s1vjF */,_11T/* Text.ParserCombinators.ReadPrec.minPrec */, _1ng/* s1vkp */));
        });
        return B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_1mS/* s1vjH */(_2G/* GHC.Types.False */, _1nc/* s1vkh */)), _1nf/* s1vkq */));
      });
      return B(_11m/* Text.Read.Lex.expect2 */(function(_1nj/* s1vkr */){
        var _1nk/* s1vks */ = E(_1nj/* s1vkr */);
        return (_1nk/* s1vks */._==2) ? (!B(_Lg/* GHC.Base.eqString */(_1nk/* s1vks */.a, _1mO/* GHC.Read.lvl6 */))) ? new T0(2) : E(_1ne/* s1vkj */) : new T0(2);
      }));
    }),
    _1nl/* s1vkw */ = function(_1nm/* s1vkx */){
      return E(_1nd/* s1vki */);
    };
    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1nn/* s1vky */){
      return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1nn/* s1vky */, _1nl/* s1vkw */);});
    }), new T(function(){
      return new T1(1,B(_11U/* GHC.Read.$wa3 */(_1n8/* s1vkd */, _1nc/* s1vkh */)));
    }));});
  };
  return new F(function(){return _1nb/* s1vke */(_1mR/* s1vjG */);});
},
_1no/* a7 */ = function(_1np/* s1vpn */, _1nq/* s1vpo */){
  return new F(function(){return _1nr/* GHC.Read.$wa19 */(_1nq/* s1vpo */);});
},
_1nr/* $wa19 */ = function(_1ns/* s1vpp */){
  var _1nt/* s1vpu */ = new T(function(){
    return B(_11m/* Text.Read.Lex.expect2 */(function(_1nu/* s1vpr */){
      var _1nv/* s1vps */ = E(_1nu/* s1vpr */);
      if(_1nv/* s1vps */._==1){
        return new F(function(){return A1(_1ns/* s1vpp */,_1nv/* s1vps */.a);});
      }else{
        return new T0(2);
      }
    }));
  }),
  _1nw/* s1vpv */ = function(_1nx/* s1vpw */){
    return E(_1nt/* s1vpu */);
  };
  return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(B(_PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,function(_1ny/* s1vpx */){
    return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1ny/* s1vpx */, _1nw/* s1vpv */);});
  }), new T(function(){
    return B(_1mP/* GHC.Read.$wa */(_1mL/* GHC.Read.$fReadChar2 */, _1ns/* s1vpp */));
  }))), new T(function(){
    return new T1(1,B(_11U/* GHC.Read.$wa3 */(_1no/* GHC.Read.a7 */, _1ns/* s1vpp */)));
  }));});
},
_1nz/* $fReadChar1 */ = function(_1nA/* s1vpF */, _1nB/* s1vpG */){
  return new F(function(){return _1nr/* GHC.Read.$wa19 */(_1nB/* s1vpG */);});
},
_1nC/* $fRead[]3 */ = function(_1nD/* s1vpI */, _1nE/* s1vpJ */){
  return new F(function(){return _1mP/* GHC.Read.$wa */(_1nz/* GHC.Read.$fReadChar1 */, _1nE/* s1vpJ */);});
},
_1nF/* $fRead[]5 */ = new T(function(){
  return B(_1mP/* GHC.Read.$wa */(_1nz/* GHC.Read.$fReadChar1 */, _R2/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1nG/* $fRead[]4 */ = function(_1nH/* B1 */){
  return new F(function(){return _OM/* Text.ParserCombinators.ReadP.run */(_1nF/* GHC.Read.$fRead[]5 */, _1nH/* B1 */);});
},
_1nI/* $fReadChar4 */ = new T(function(){
  return B(_1nr/* GHC.Read.$wa19 */(_R2/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1nJ/* $fReadChar3 */ = function(_1nH/* B1 */){
  return new F(function(){return _OM/* Text.ParserCombinators.ReadP.run */(_1nI/* GHC.Read.$fReadChar4 */, _1nH/* B1 */);});
},
_1nK/* $fRead[]_$s$creadsPrec1 */ = function(_1nL/* s1vpH */, _1nH/* B1 */){
  return new F(function(){return _1nJ/* GHC.Read.$fReadChar3 */(_1nH/* B1 */);});
},
_1nM/* $fRead[]_$s$fRead[]1 */ = new T4(0,_1nK/* GHC.Read.$fRead[]_$s$creadsPrec1 */,_1nG/* GHC.Read.$fRead[]4 */,_1nz/* GHC.Read.$fReadChar1 */,_1nC/* GHC.Read.$fRead[]3 */),
_1nN/* $fRead(,)6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(","));
}),
_1nO/* readPrec */ = function(_1nP/* s1vgA */){
  return E(E(_1nP/* s1vgA */).c);
},
_1nQ/* $fRead(,)5 */ = function(_1nR/* s1vtd */, _1nS/* s1vte */, _1nT/* s1vtf */){
  var _1nU/* s1vtg */ = new T(function(){
    return B(_1nO/* GHC.Read.readPrec */(_1nS/* s1vte */));
  }),
  _1nV/* s1vth */ = new T(function(){
    return B(A2(_1nO/* GHC.Read.readPrec */,_1nR/* s1vtd */, _1nT/* s1vtf */));
  }),
  _1nW/* s1vtz */ = function(_1nX/* s1vti */){
    var _1nY/* s1vty */ = function(_1nZ/* s1vtj */){
      var _1o0/* s1vtk */ = new T(function(){
        var _1o1/* s1vtl */ = new T(function(){
          return B(A2(_1nU/* s1vtg */,_1nT/* s1vtf */, function(_1o2/* s1vtm */){
            return new F(function(){return A1(_1nX/* s1vti */,new T2(0,_1nZ/* s1vtj */,_1o2/* s1vtm */));});
          }));
        });
        return B(_11m/* Text.Read.Lex.expect2 */(function(_1o3/* s1vtp */){
          var _1o4/* s1vtq */ = E(_1o3/* s1vtp */);
          return (_1o4/* s1vtq */._==2) ? (!B(_Lg/* GHC.Base.eqString */(_1o4/* s1vtq */.a, _1nN/* GHC.Read.$fRead(,)6 */))) ? new T0(2) : E(_1o1/* s1vtl */) : new T0(2);
        }));
      }),
      _1o5/* s1vtu */ = function(_1o6/* s1vtv */){
        return E(_1o0/* s1vtk */);
      };
      return new T1(1,function(_1o7/* s1vtw */){
        return new F(function(){return A2(_103/* Text.ParserCombinators.ReadP.skipSpaces_skip */,_1o7/* s1vtw */, _1o5/* s1vtu */);});
      });
    };
    return new F(function(){return A1(_1nV/* s1vth */,_1nY/* s1vty */);});
  };
  return E(_1nW/* s1vtz */);
},
_1o8/* $wa2 */ = function(_1o9/* s1vuR */, _1oa/* s1vuS */, _1ob/* s1vuT */){
  var _1oc/* s1vuU */ = function(_1nH/* B1 */){
    return new F(function(){return _1nQ/* GHC.Read.$fRead(,)5 */(_1o9/* s1vuR */, _1oa/* s1vuS */, _1nH/* B1 */);});
  },
  _1od/* s1vuV */ = function(_1oe/* s1vuX */, _1of/* s1vuY */){
    return new F(function(){return _1og/* s1vuW */(_1of/* s1vuY */);});
  },
  _1og/* s1vuW */ = function(_1oh/* s1vuZ */){
    return new F(function(){return _PW/* Text.ParserCombinators.ReadP.$fAlternativeP_$c<|> */(new T1(1,B(_11U/* GHC.Read.$wa3 */(_1oc/* s1vuU */, _1oh/* s1vuZ */))), new T(function(){
      return new T1(1,B(_11U/* GHC.Read.$wa3 */(_1od/* s1vuV */, _1oh/* s1vuZ */)));
    }));});
  };
  return new F(function(){return _1og/* s1vuW */(_1ob/* s1vuT */);});
},
_1oi/* $s$fRead(,)3 */ = function(_1oj/* sibV */, _1ok/* sibW */){
  return new F(function(){return _1o8/* GHC.Read.$wa2 */(_1nM/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1nM/* GHC.Read.$fRead[]_$s$fRead[]1 */, _1ok/* sibW */);});
},
_1ol/* lvl10 */ = new T(function(){
  return B(_1mP/* GHC.Read.$wa */(_1oi/* Main.$s$fRead(,)3 */, _12Y/* Text.Read.readEither5 */));
}),
_1om/* lvl13 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("Error generating tabs"));
}),
_1on/* lookup */ = function(_1oo/* s9uF */, _1op/* s9uG */, _1oq/* s9uH */){
  while(1){
    var _1or/* s9uI */ = E(_1oq/* s9uH */);
    if(!_1or/* s9uI */._){
      return __Z/* EXTERNAL */;
    }else{
      var _1os/* s9uL */ = E(_1or/* s9uI */.a);
      if(!B(A3(_Up/* GHC.Classes.== */,_1oo/* s9uF */, _1op/* s9uG */, _1os/* s9uL */.a))){
        _1oq/* s9uH */ = _1or/* s9uI */.b;
        continue;
      }else{
        return new T1(1,_1os/* s9uL */.b);
      }
    }
  }
},
_1ot/* getMaybeNumberFIUnitValue */ = function(_1ou/* sekT */, _1ov/* sekU */){
  var _1ow/* sekV */ = E(_1ov/* sekU */);
  if(!_1ow/* sekV */._){
    return __Z/* EXTERNAL */;
  }else{
    var _1ox/* sekX */ = E(_1ou/* sekT */);
    if(_1ox/* sekX */._==3){
      var _1oy/* sel1 */ = E(_1ox/* sekX */.b);
      switch(_1oy/* sel1 */._){
        case 0:
          return new T1(1,_1oy/* sel1 */.a);
        case 1:
          return new F(function(){return _1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_12/* GHC.Base.++ */(B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1ox/* sekX */.a).b)), _OE/* FormEngine.FormItem.nfiUnitId1 */));
          }), _1ow/* sekV */.a);});
          break;
        default:
          return __Z/* EXTERNAL */;
      }
    }else{
      return E(_16T/* FormEngine.FormItem.nfiUnit1 */);
    }
  }
},
_1oz/* fiId */ = function(_1oA/* s5vK */){
  return new F(function(){return _4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1oA/* s5vK */)).b);});
},
_1oB/* isCheckboxChecked1 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("on"));
}),
_1oC/* isCheckboxChecked */ = function(_1oD/* sekM */, _1oE/* sekN */){
  var _1oF/* sekO */ = E(_1oE/* sekN */);
  if(!_1oF/* sekO */._){
    return false;
  }else{
    var _1oG/* sekR */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_1oz/* FormEngine.FormItem.fiId */(_1oD/* sekM */));
    }), _1oF/* sekO */.a));
    if(!_1oG/* sekR */._){
      return false;
    }else{
      return new F(function(){return _Lg/* GHC.Base.eqString */(_1oG/* sekR */.a, _1oB/* FormEngine.FormData.isCheckboxChecked1 */);});
    }
  }
},
_1oH/* isOptionSelected */ = function(_1oI/* sekk */, _1oJ/* sekl */, _1oK/* sekm */){
  var _1oL/* sekn */ = E(_1oK/* sekm */);
  if(!_1oL/* sekn */._){
    return false;
  }else{
    var _1oM/* sekA */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
      return B(_4Q/* FormEngine.FormItem.numbering2text */(B(_4f/* FormEngine.FormItem.fiDescriptor */(_1oJ/* sekl */)).b));
    }), _1oL/* sekn */.a));
    if(!_1oM/* sekA */._){
      return false;
    }else{
      var _1oN/* sekB */ = _1oM/* sekA */.a,
      _1oO/* sekC */ = E(_1oI/* sekk */);
      if(!_1oO/* sekC */._){
        return new F(function(){return _Lg/* GHC.Base.eqString */(_1oN/* sekB */, _1oO/* sekC */.a);});
      }else{
        return new F(function(){return _Lg/* GHC.Base.eqString */(_1oN/* sekB */, _1oO/* sekC */.b);});
      }
    }
  }
},
_1oP/* mapMaybe */ = function(_1oQ/*  s7rs */, _1oR/*  s7rt */){
  while(1){
    var _1oS/*  mapMaybe */ = B((function(_1oT/* s7rs */, _1oU/* s7rt */){
      var _1oV/* s7ru */ = E(_1oU/* s7rt */);
      if(!_1oV/* s7ru */._){
        return __Z/* EXTERNAL */;
      }else{
        var _1oW/* s7rw */ = _1oV/* s7ru */.b,
        _1oX/* s7rx */ = B(A1(_1oT/* s7rs */,_1oV/* s7ru */.a));
        if(!_1oX/* s7rx */._){
          var _1oY/*   s7rs */ = _1oT/* s7rs */;
          _1oQ/*  s7rs */ = _1oY/*   s7rs */;
          _1oR/*  s7rt */ = _1oW/* s7rw */;
          return __continue/* EXTERNAL */;
        }else{
          return new T2(1,_1oX/* s7rx */.a,new T(function(){
            return B(_1oP/* Data.Maybe.mapMaybe */(_1oT/* s7rs */, _1oW/* s7rw */));
          }));
        }
      }
    })(_1oQ/*  s7rs */, _1oR/*  s7rt */));
    if(_1oS/*  mapMaybe */!=__continue/* EXTERNAL */){
      return _1oS/*  mapMaybe */;
    }
  }
},
_1oZ/* maybeStr2maybeInt2 */ = new T(function(){
  return B(A3(_12o/* GHC.Read.$fReadInt3 */,_12R/* GHC.Read.$fReadInt_$sconvertInt */, _11T/* Text.ParserCombinators.ReadPrec.minPrec */, _R2/* Text.ParserCombinators.ReadP.$fApplicativeP_$creturn */));
}),
_1p0/* maybeStr2maybeInt1 */ = function(_1p1/* s65V */){
  var _1p2/* s65W */ = B(_OM/* Text.ParserCombinators.ReadP.run */(_1oZ/* FormEngine.FormElement.FormElement.maybeStr2maybeInt2 */, _1p1/* s65V */));
  return (_1p2/* s65W */._==0) ? __Z/* EXTERNAL */ : (E(_1p2/* s65W */.b)._==0) ? new T1(1,E(_1p2/* s65W */.a).a) : __Z/* EXTERNAL */;
},
_1p3/* makeElem */ = function(_1p4/* s668 */, _1p5/* s669 */, _1p6/* s66a */){
  var _1p7/* s66b */ = E(_1p6/* s66a */);
  switch(_1p7/* s66b */._){
    case 0:
      var _1p8/* s66s */ = new T(function(){
        var _1p9/* s66d */ = E(_1p5/* s669 */);
        if(!_1p9/* s66d */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1pa/* s66q */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1p7/* s66b */.a).b));
          }), _1p9/* s66d */.a));
          if(!_1pa/* s66q */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1pa/* s66q */.a);
          }
        }
      });
      return new T1(1,new T3(1,_1p7/* s66b */,_1p8/* s66s */,_1p4/* s668 */));
    case 1:
      var _1pb/* s66K */ = new T(function(){
        var _1pc/* s66v */ = E(_1p5/* s669 */);
        if(!_1pc/* s66v */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1pd/* s66I */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1p7/* s66b */.a).b));
          }), _1pc/* s66v */.a));
          if(!_1pd/* s66I */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1pd/* s66I */.a);
          }
        }
      });
      return new T1(1,new T3(2,_1p7/* s66b */,_1pb/* s66K */,_1p4/* s668 */));
    case 2:
      var _1pe/* s672 */ = new T(function(){
        var _1pf/* s66N */ = E(_1p5/* s669 */);
        if(!_1pf/* s66N */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1pg/* s670 */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1p7/* s66b */.a).b));
          }), _1pf/* s66N */.a));
          if(!_1pg/* s670 */._){
            return __Z/* EXTERNAL */;
          }else{
            return E(_1pg/* s670 */.a);
          }
        }
      });
      return new T1(1,new T3(3,_1p7/* s66b */,_1pe/* s672 */,_1p4/* s668 */));
    case 3:
      var _1ph/* s67l */ = new T(function(){
        var _1pi/* s676 */ = E(_1p5/* s669 */);
        if(!_1pi/* s676 */._){
          return __Z/* EXTERNAL */;
        }else{
          var _1pj/* s67j */ = B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1p7/* s66b */.a).b));
          }), _1pi/* s676 */.a));
          if(!_1pj/* s67j */._){
            return __Z/* EXTERNAL */;
          }else{
            return B(_1p0/* FormEngine.FormElement.FormElement.maybeStr2maybeInt1 */(_1pj/* s67j */.a));
          }
        }
      });
      return new T1(1,new T4(4,_1p7/* s66b */,_1ph/* s67l */,new T(function(){
        return B(_1ot/* FormEngine.FormData.getMaybeNumberFIUnitValue */(_1p7/* s66b */, _1p5/* s669 */));
      }),_1p4/* s668 */));
    case 4:
      return new T1(1,new T2(5,_1p7/* s66b */,_1p4/* s668 */));
    case 5:
      var _1pk/* s67t */ = new T(function(){
        return new T3(6,_1p7/* s66b */,_1pl/* s67u */,_1p4/* s668 */);
      }),
      _1pl/* s67u */ = new T(function(){
        var _1pm/* s67F */ = function(_1pn/* s67v */){
          var _1po/* s67w */ = E(_1pn/* s67v */);
          if(!_1po/* s67w */._){
            return new T2(0,_1po/* s67w */,new T(function(){
              return B(_1oH/* FormEngine.FormData.isOptionSelected */(_1po/* s67w */, _1p7/* s66b */, _1p5/* s669 */));
            }));
          }else{
            var _1pp/* s67E */ = new T(function(){
              return B(_1oP/* Data.Maybe.mapMaybe */(function(_1pq/* B1 */){
                return new F(function(){return _1p3/* FormEngine.FormElement.FormElement.makeElem */(_1pk/* s67t */, _1p5/* s669 */, _1pq/* B1 */);});
              }, _1po/* s67w */.c));
            });
            return new T3(1,_1po/* s67w */,new T(function(){
              return B(_1oH/* FormEngine.FormData.isOptionSelected */(_1po/* s67w */, _1p7/* s66b */, _1p5/* s669 */));
            }),_1pp/* s67E */);
          }
        };
        return B(_2S/* GHC.Base.map */(_1pm/* s67F */, _1p7/* s66b */.b));
      });
      return new T1(1,_1pk/* s67t */);
    case 6:
      var _1pr/* s67V */ = new T(function(){
        var _1ps/* s67I */ = E(_1p5/* s669 */);
        if(!_1ps/* s67I */._){
          return __Z/* EXTERNAL */;
        }else{
          return B(_1on/* GHC.List.lookup */(_QP/* GHC.Classes.$fEq[]_$s$fEq[]1 */, new T(function(){
            return B(_4Q/* FormEngine.FormItem.numbering2text */(E(_1p7/* s66b */.a).b));
          }), _1ps/* s67I */.a));
        }
      });
      return new T1(1,new T3(7,_1p7/* s66b */,_1pr/* s67V */,_1p4/* s668 */));
    case 7:
      return __Z/* EXTERNAL */;
    case 8:
      var _1pt/* s682 */ = new T(function(){
        return new T3(8,_1p7/* s66b */,_1pu/* s683 */,_1p4/* s668 */);
      }),
      _1pu/* s683 */ = new T(function(){
        return B(_1oP/* Data.Maybe.mapMaybe */(function(_1pq/* B1 */){
          return new F(function(){return _1p3/* FormEngine.FormElement.FormElement.makeElem */(_1pt/* s682 */, _1p5/* s669 */, _1pq/* B1 */);});
        }, _1p7/* s66b */.c));
      });
      return new T1(1,_1pt/* s682 */);
    case 9:
      var _1pv/* s689 */ = new T(function(){
        return new T4(9,_1p7/* s66b */,new T(function(){
          return B(_1oC/* FormEngine.FormData.isCheckboxChecked */(_1p7/* s66b */, _1p5/* s669 */));
        }),_1pw/* s68a */,_1p4/* s668 */);
      }),
      _1pw/* s68a */ = new T(function(){
        return B(_1oP/* Data.Maybe.mapMaybe */(function(_1pq/* B1 */){
          return new F(function(){return _1p3/* FormEngine.FormElement.FormElement.makeElem */(_1pv/* s689 */, _1p5/* s669 */, _1pq/* B1 */);});
        }, _1p7/* s66b */.c));
      });
      return new T1(1,_1pv/* s689 */);
    case 10:
      var _1px/* s68f */ = new T(function(){
        return new T3(10,_1p7/* s66b */,_1py/* s68g */,_1p4/* s668 */);
      }),
      _1py/* s68g */ = new T(function(){
        return B(_1oP/* Data.Maybe.mapMaybe */(function(_1pq/* B1 */){
          return new F(function(){return _1p3/* FormEngine.FormElement.FormElement.makeElem */(_1px/* s68f */, _1p5/* s669 */, _1pq/* B1 */);});
        }, _1p7/* s66b */.c));
      });
      return new T1(1,_1px/* s68f */);
    case 11:
      return new T1(1,new T2(11,_1p7/* s66b */,_1p4/* s668 */));
    default:
      return new T1(1,new T2(12,_1p7/* s66b */,_1p4/* s668 */));
  }
},
_1pz/* onResize2 */ = "(function (ev, jq) { jq.resize(ev); })",
_1pA/* onResize1 */ = function(_1pB/* snCd */, _1pC/* snCe */, _/* EXTERNAL */){
  var _1pD/* snCq */ = __createJSFunc/* EXTERNAL */(2, function(_1pE/* snCh */, _/* EXTERNAL */){
    var _1pF/* snCj */ = B(A2(E(_1pB/* snCd */),_1pE/* snCh */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1pG/* snCt */ = E(_1pC/* snCe */),
  _1pH/* snCy */ = eval/* EXTERNAL */(E(_1pz/* FormEngine.JQuery.onResize2 */)),
  _1pI/* snCG */ = E(_1pH/* snCy */)(_1pD/* snCq */, _1pG/* snCt */);
  return _1pG/* snCt */;
},
_1pJ/* onScroll2 */ = "(function (ev, jq) { jq.scroll(ev); })",
_1pK/* onScroll1 */ = function(_1pL/* snCM */, _1pM/* snCN */, _/* EXTERNAL */){
  var _1pN/* snCZ */ = __createJSFunc/* EXTERNAL */(2, function(_1pO/* snCQ */, _/* EXTERNAL */){
    var _1pP/* snCS */ = B(A2(E(_1pL/* snCM */),_1pO/* snCQ */, _/* EXTERNAL */));
    return _3e/* Haste.Prim.Any.jsNull */;
  }),
  _1pQ/* snD2 */ = E(_1pM/* snCN */),
  _1pR/* snD7 */ = eval/* EXTERNAL */(E(_1pJ/* FormEngine.JQuery.onScroll2 */)),
  _1pS/* snDf */ = E(_1pR/* snD7 */)(_1pN/* snCZ */, _1pQ/* snD2 */);
  return _1pQ/* snD2 */;
},
_1pT/* pageTabGroup17 */ = 600,
_1pU/* pageTabGroup16 */ = new T2(1,_1pT/* Page.pageTabGroup17 */,_I/* GHC.Types.[] */),
_1pV/* pageTabGroup15 */ = new T2(1,_1pU/* Page.pageTabGroup16 */,_2H/* Page.pageTabGroup10 */),
_1pW/* pageTabGroup14 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1pV/* Page.pageTabGroup15 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1pX/* pageTabGroup13 */ = new T2(7,_1pW/* Page.pageTabGroup14 */,_I/* GHC.Types.[] */),
_1pY/* mQuestionnaireTab */ = new T3(0,_1pX/* Page.pageTabGroup13 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1pZ/* pageTabGroup12 */ = 700,
_1q0/* pageTabGroup11 */ = new T2(1,_1pZ/* Page.pageTabGroup12 */,_I/* GHC.Types.[] */),
_1q1/* pageTabGroup9 */ = new T2(1,_1q0/* Page.pageTabGroup11 */,_2H/* Page.pageTabGroup10 */),
_1q2/* pageTabGroup8 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1q1/* Page.pageTabGroup9 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1q3/* pageTabGroup7 */ = new T2(7,_1q2/* Page.pageTabGroup8 */,_I/* GHC.Types.[] */),
_1q4/* tQuestionnaireTab */ = new T3(0,_1q3/* Page.pageTabGroup7 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1q5/* pageTabGroup6 */ = new T2(1,_1q4/* Page.tQuestionnaireTab */,_I/* GHC.Types.[] */),
_1q6/* pageTabGroup5 */ = new T2(1,_1pY/* Page.mQuestionnaireTab */,_1q5/* Page.pageTabGroup6 */),
_1q7/* pageTabGroup22 */ = 500,
_1q8/* pageTabGroup21 */ = new T2(1,_1q7/* Page.pageTabGroup22 */,_I/* GHC.Types.[] */),
_1q9/* pageTabGroup20 */ = new T2(1,_1q8/* Page.pageTabGroup21 */,_2H/* Page.pageTabGroup10 */),
_1qa/* pageTabGroup19 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1q9/* Page.pageTabGroup20 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1qb/* pageTabGroup18 */ = new T2(7,_1qa/* Page.pageTabGroup19 */,_I/* GHC.Types.[] */),
_1qc/* rolesTab */ = new T3(0,_1qb/* Page.pageTabGroup18 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1qd/* pageTabGroup4 */ = new T2(1,_1qc/* Page.rolesTab */,_1q6/* Page.pageTabGroup5 */),
_1qe/* pageTabGroup3 */ = new T2(1,_3R/* Page.dataTab */,_1qd/* Page.pageTabGroup4 */),
_1qf/* pageTabGroup2 */ = new T2(1,_3Z/* Page.lifecycleTab */,_1qe/* Page.pageTabGroup3 */),
_1qg/* pageTabGroup1 */ = new T2(1,_2N/* Page.actionTab */,_1qf/* Page.pageTabGroup2 */),
_1qh/* pageTabGroup42 */ = 100,
_1qi/* pageTabGroup41 */ = new T2(1,_1qh/* Page.pageTabGroup42 */,_I/* GHC.Types.[] */),
_1qj/* pageTabGroup40 */ = new T2(1,_1qi/* Page.pageTabGroup41 */,_2H/* Page.pageTabGroup10 */),
_1qk/* pageTabGroup39 */ = {_:0,a:_2o/* GHC.Base.Nothing */,b:_1qj/* Page.pageTabGroup40 */,c:_2o/* GHC.Base.Nothing */,d:_I/* GHC.Types.[] */,e:_2o/* GHC.Base.Nothing */,f:_2o/* GHC.Base.Nothing */,g:_2o/* GHC.Base.Nothing */,h:_2G/* GHC.Types.False */,i:_I/* GHC.Types.[] */},
_1ql/* pageTabGroup38 */ = new T2(7,_1qk/* Page.pageTabGroup39 */,_I/* GHC.Types.[] */),
_1qm/* visionTab */ = new T3(0,_1ql/* Page.pageTabGroup38 */,_I/* GHC.Types.[] */,_2G/* GHC.Types.False */),
_1qn/* pageTabGroup */ = new T2(1,_1qm/* Page.visionTab */,_1qg/* Page.pageTabGroup1 */),
_1qo/* getWidth_f1 */ = new T(function(){
  return (function (jq) { return jq.width(); });
}),
_1qp/* resizeHandler2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".svg-help"));
}),
_1qq/* resizeHandler_paneSel */ = new T(function(){
  return B(unCStr/* EXTERNAL */(".desc-subpane"));
}),
_1qr/* setWidth_f1 */ = new T(function(){
  return (function (val, jq) { jq.width(val); return jq; });
}),
_1qs/* $wa */ = function(_/* EXTERNAL */){
  var _1qt/* sidC */ = __app0/* EXTERNAL */(E(_7q/* FormEngine.JQuery.getWindow_f1 */)),
  _1qu/* sidI */ = __app1/* EXTERNAL */(E(_1qo/* FormEngine.JQuery.getWidth_f1 */), _1qt/* sidC */),
  _1qv/* sidL */ = B(_7v/* FormEngine.JQuery.select1 */(_1qq/* Main.resizeHandler_paneSel */, _/* EXTERNAL */)),
  _1qw/* sidP */ = Number/* EXTERNAL */(_1qu/* sidI */),
  _1qx/* sidT */ = jsTrunc/* EXTERNAL */(_1qw/* sidP */),
  _1qy/* sie4 */ = E(_1qr/* FormEngine.JQuery.setWidth_f1 */),
  _1qz/* sie7 */ = __app2/* EXTERNAL */(_1qy/* sie4 */, _1qx/* sidT */-790|0, E(_1qv/* sidL */)),
  _1qA/* siea */ = B(_7v/* FormEngine.JQuery.select1 */(_1qp/* Main.resizeHandler2 */, _/* EXTERNAL */)),
  _1qB/* sieg */ = __app2/* EXTERNAL */(_1qy/* sie4 */, _1qx/* sidT */-795|0, E(_1qA/* siea */));
  return _0/* GHC.Tuple.() */;
},
_1qC/* resizeHandler1 */ = function(_1qD/* siej */, _/* EXTERNAL */){
  return new F(function(){return _1qs/* Main.$wa */(_/* EXTERNAL */);});
},
_1qE/* time2 */ = "(function (label) { console.time(label); })",
_1qF/* time1 */ = function(_1qG/* snAa */, _/* EXTERNAL */){
  var _1qH/* snAk */ = eval/* EXTERNAL */(E(_1qE/* FormEngine.JQuery.time2 */)),
  _1qI/* snAs */ = E(_1qH/* snAk */)(toJSStr/* EXTERNAL */(E(_1qG/* snAa */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1qJ/* timeEnd2 */ = "(function (label) { console.timeEnd(label); })",
_1qK/* timeEnd1 */ = function(_1qL/* snzM */, _/* EXTERNAL */){
  var _1qM/* snzW */ = eval/* EXTERNAL */(E(_1qJ/* FormEngine.JQuery.timeEnd2 */)),
  _1qN/* snA4 */ = E(_1qM/* snzW */)(toJSStr/* EXTERNAL */(E(_1qL/* snzM */)));
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1qO/* lvl14 */ = function(_1qP/* sieO */, _/* EXTERNAL */){
  var _1qQ/* sieR */ = new T(function(){
    var _1qR/* sieW */ = B(_OF/* Text.Read.readEither6 */(B(_OM/* Text.ParserCombinators.ReadP.run */(_1ol/* Main.lvl10 */, new T(function(){
      var _1qS/* sieS */ = E(_1qP/* sieO */);
      if(!_1qS/* sieS */._){
        return __Z/* EXTERNAL */;
      }else{
        return E(_1qS/* sieS */.a);
      }
    })))));
    if(!_1qR/* sieW */._){
      return __Z/* EXTERNAL */;
    }else{
      if(!E(_1qR/* sieW */.b)._){
        return new T1(1,_1qR/* sieW */.a);
      }else{
        return __Z/* EXTERNAL */;
      }
    }
  }),
  _1qT/* sif9 */ = function(_1qU/* sif2 */){
    var _1qV/* sif3 */ = E(_1qU/* sif2 */);
    if(_1qV/* sif3 */._==7){
      var _1qW/* sif6 */ = new T(function(){
        return new T3(0,_1qV/* sif3 */,_1qX/* sif7 */,_2G/* GHC.Types.False */);
      }),
      _1qX/* sif7 */ = new T(function(){
        return B(_1oP/* Data.Maybe.mapMaybe */(function(_1qY/* B1 */){
          return new F(function(){return _1p3/* FormEngine.FormElement.FormElement.makeElem */(_1qW/* sif6 */, _1qQ/* sieR */, _1qY/* B1 */);});
        }, _1qV/* sif3 */.b));
      });
      return new T1(1,_1qW/* sif6 */);
    }else{
      return __Z/* EXTERNAL */;
    }
  },
  _1qZ/* sieQ */ = B(_2S/* GHC.Base.map */(_1qT/* sif9 */, _JS/* FormStructure.FormStructure.formItems */));
  if(!B(_1mw/* Main.go */(_1qZ/* sieQ */))){
    var _1r0/* sifb */ = B(_87/* Data.Maybe.catMaybes1 */(_1qZ/* sieQ */)),
    _1r1/* sifd */ = B(_8f/* FormEngine.JQuery.dumptIO1 */(B(_26/* GHC.Show.showList__ */(_6L/* FormEngine.FormElement.FormElement.$fShowFormElement1 */, _1r0/* sifb */, _I/* GHC.Types.[] */)), _/* EXTERNAL */)),
    _1r2/* sifg */ = B(_1qF/* FormEngine.JQuery.time1 */(_1mz/* Main.lvl */, _/* EXTERNAL */)),
    _1r3/* sifj */ = B(_1lQ/* Form.generateQuestionnaire1 */(_1r0/* sifb */, _/* EXTERNAL */)),
    _1r4/* sifm */ = B(_1qK/* FormEngine.JQuery.timeEnd1 */(_1mz/* Main.lvl */, _/* EXTERNAL */)),
    _1r5/* sifp */ = E(_7q/* FormEngine.JQuery.getWindow_f1 */),
    _1r6/* sifs */ = __app0/* EXTERNAL */(_1r5/* sifp */),
    _1r7/* sifz */ = B(_1pK/* FormEngine.JQuery.onScroll1 */(function(_1r8/* sifv */, _/* EXTERNAL */){
      return new F(function(){return _7y/* Main.$wa1 */(_1r0/* sifb */, _/* EXTERNAL */);});
    }, _1r6/* sifs */, _/* EXTERNAL */)),
    _1r9/* sifD */ = __app0/* EXTERNAL */(_1r5/* sifp */),
    _1ra/* sifH */ = B(_1pA/* FormEngine.JQuery.onResize1 */(_1qC/* Main.resizeHandler1 */, _1r9/* sifD */, _/* EXTERNAL */)),
    _1rb/* sifL */ = __app0/* EXTERNAL */(_1r5/* sifp */),
    _1rc/* sifO */ = B(_83/* FormEngine.JQuery.$wa17 */(_1rb/* sifL */, _/* EXTERNAL */)),
    _1rd/* sifR */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_1qm/* Page.visionTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }else{
    var _1re/* sifU */ = B(_8k/* FormEngine.JQuery.errorIO1 */(_1om/* Main.lvl13 */, _/* EXTERNAL */));
    return _0/* GHC.Tuple.() */;
  }
},
_1rf/* lvl15 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_investigator"));
}),
_1rg/* lvl16 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_manager"));
}),
_1rh/* lvl17 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_steward"));
}),
_1ri/* lvl18 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_custodian"));
}),
_1rj/* lvl19 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_curator"));
}),
_1rk/* lvl20 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_consumer"));
}),
_1rl/* lvl21 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_expert"));
}),
_1rm/* lvl22 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_producer"));
}),
_1rn/* lvl23 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_public"));
}),
_1ro/* lvl24 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_secondary"));
}),
_1rp/* lvl25 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_primary"));
}),
_1rq/* lvl26 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("#svg_raw"));
}),
_1rr/* overlay2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("margin-top"));
}),
_1rs/* overlay3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("body"));
}),
_1rt/* overlay4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("div"));
}),
_1ru/* $w$j */ = function(_/* EXTERNAL */, _1rv/* sJNt */){
  var _1rw/* sJNu */ = B(_18S/* FormEngine.JQuery.$wa9 */(_1rt/* Overlay.overlay4 */, _1rv/* sJNt */, _/* EXTERNAL */)),
  _1rx/* sJNx */ = B(_7v/* FormEngine.JQuery.select1 */(_1rs/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1ry/* sJNF */ = E(_7o/* FormEngine.JQuery.getScrollTop_f1 */)(E(_1rx/* sJNx */)),
  _1rz/* sJNJ */ = Number/* EXTERNAL */(_1ry/* sJNF */),
  _1rA/* sJNN */ = jsTrunc/* EXTERNAL */(_1rz/* sJNJ */);
  return new F(function(){return _77/* FormEngine.JQuery.$wa2 */(_1rr/* Overlay.overlay2 */, B(_4a/* GHC.Show.$wshowSignedInt */(0, _1rA/* sJNN */+25|0, _I/* GHC.Types.[] */)), E(_1rw/* sJNu */), _/* EXTERNAL */);});
},
_1rB/* getCss2 */ = "(function (key, jq) { return jq.css(key); })",
_1rC/* $wa11 */ = function(_1rD/* snSA */, _1rE/* snSB */, _/* EXTERNAL */){
  var _1rF/* snSL */ = eval/* EXTERNAL */(E(_1rB/* FormEngine.JQuery.getCss2 */)),
  _1rG/* snST */ = E(_1rF/* snSL */)(toJSStr/* EXTERNAL */(E(_1rD/* snSA */)), _1rE/* snSB */);
  return new T(function(){
    return String/* EXTERNAL */(_1rG/* snST */);
  });
},
_1rH/* getHeight_f1 */ = new T(function(){
  return (function (jq) { return jq.height(); });
}),
_1rI/* hideJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("hidden"));
}),
_1rJ/* hideJq3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1rK/* overlay5 */ = "visible",
_1rL/* overlay6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visibility"));
}),
_1rM/* setHeight_f1 */ = new T(function(){
  return (function (val, jq) { jq.height(val); return jq; });
}),
_1rN/* showJq2 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("visible"));
}),
_1rO/* overlay1 */ = function(_1rP/* sJNU */, _/* EXTERNAL */){
  var _1rQ/* sJNX */ = B(_7v/* FormEngine.JQuery.select1 */(B(unAppCStr/* EXTERNAL */("#", _1rP/* sJNU */)), _/* EXTERNAL */)),
  _1rR/* sJO0 */ = B(_7v/* FormEngine.JQuery.select1 */(_1rs/* Overlay.overlay3 */, _/* EXTERNAL */)),
  _1rS/* sJO8 */ = E(_1rH/* FormEngine.JQuery.getHeight_f1 */)(E(_1rR/* sJO0 */)),
  _1rT/* sJOc */ = Number/* EXTERNAL */(_1rS/* sJO8 */),
  _1rU/* sJOg */ = jsTrunc/* EXTERNAL */(_1rT/* sJOc */),
  _1rV/* sJOq */ = E(_1rM/* FormEngine.JQuery.setHeight_f1 */)(_1rU/* sJOg */, E(_1rQ/* sJNX */)),
  _1rW/* sJOt */ = B(_1rC/* FormEngine.JQuery.$wa11 */(_1rL/* Overlay.overlay6 */, _1rV/* sJOq */, _/* EXTERNAL */)),
  _1rX/* sJOB */ = strEq/* EXTERNAL */(E(_1rW/* sJOt */), E(_1rK/* Overlay.overlay5 */));
  if(!E(_1rX/* sJOB */)){
    var _1rY/* sJOK */ = B(_77/* FormEngine.JQuery.$wa2 */(_1rJ/* FormEngine.JQuery.hideJq3 */, _1rN/* FormEngine.JQuery.showJq2 */, _1rV/* sJOq */, _/* EXTERNAL */));
    return new F(function(){return _1ru/* Overlay.$w$j */(_/* EXTERNAL */, E(_1rY/* sJOK */));});
  }else{
    var _1rZ/* sJOF */ = B(_77/* FormEngine.JQuery.$wa2 */(_1rJ/* FormEngine.JQuery.hideJq3 */, _1rI/* FormEngine.JQuery.hideJq2 */, _1rV/* sJOq */, _/* EXTERNAL */));
    return new F(function(){return _1ru/* Overlay.$w$j */(_/* EXTERNAL */, E(_1rZ/* sJOF */));});
  }
},
_1s0/* ready_f1 */ = new T(function(){
  return (function (f) { jQuery(document).ready(f); });
}),
_1s1/* tinkerDiagSvgConsumer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_consumer"));
}),
_1s2/* tinkerDiagSvgConsumer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lu/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1s1/* DiagramDecorator.tinkerDiagSvgConsumer3 */, _/* EXTERNAL */);});
},
_1s3/* tinkerDiagSvgConsumer1 */ = function(_1s4/* s4M7 */, _/* EXTERNAL */){
  return new F(function(){return _1s2/* DiagramDecorator.tinkerDiagSvgConsumer2 */(_/* EXTERNAL */);});
},
_1s5/* tinkerDiagSvgCurator7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_curator"));
}),
_1s6/* tinkerDiagSvgCurator2 */ = function(_/* EXTERNAL */){
  var _1s7/* s4ML */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1s8/* s4MO */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lu/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1s9/* s4MR */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1sa/* s4MU */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lx/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */)),
  _1sb/* s4MX */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lw/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lv/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1s5/* DiagramDecorator.tinkerDiagSvgCurator7 */, _/* EXTERNAL */);});
},
_1sc/* tinkerDiagSvgCurator1 */ = function(_1sd/* s4N0 */, _/* EXTERNAL */){
  return new F(function(){return _1s6/* DiagramDecorator.tinkerDiagSvgCurator2 */(_/* EXTERNAL */);});
},
_1se/* tinkerDiagSvgCustodian3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_custodian"));
}),
_1sf/* tinkerDiagSvgCustodian2 */ = function(_/* EXTERNAL */){
  var _1sg/* s4N2 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1se/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */)),
  _1sh/* s4N5 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lx/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1se/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lw/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1se/* DiagramDecorator.tinkerDiagSvgCustodian3 */, _/* EXTERNAL */);});
},
_1si/* tinkerDiagSvgCustodian1 */ = function(_1sj/* s4N8 */, _/* EXTERNAL */){
  return new F(function(){return _1sf/* DiagramDecorator.tinkerDiagSvgCustodian2 */(_/* EXTERNAL */);});
},
_1sk/* tinkerDiagSvgExpert3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_expert"));
}),
_1sl/* tinkerDiagSvgExpert2 */ = function(_/* EXTERNAL */){
  var _1sm/* s4MG */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1sk/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1sk/* DiagramDecorator.tinkerDiagSvgExpert3 */, _/* EXTERNAL */);});
},
_1sn/* tinkerDiagSvgExpert1 */ = function(_1so/* s4MJ */, _/* EXTERNAL */){
  return new F(function(){return _1sl/* DiagramDecorator.tinkerDiagSvgExpert2 */(_/* EXTERNAL */);});
},
_1sp/* tinkerDiagSvgInvestigator3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_investigator"));
}),
_1sq/* tinkerDiagSvgInvestigator2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lA/* DiagramDecorator.tinkerDiagSvgInvestigator4 */, _1sp/* DiagramDecorator.tinkerDiagSvgInvestigator3 */, _/* EXTERNAL */);});
},
_1sr/* tinkerDiagSvgInvestigator1 */ = function(_1ss/* s4M6 */, _/* EXTERNAL */){
  return new F(function(){return _1sq/* DiagramDecorator.tinkerDiagSvgInvestigator2 */(_/* EXTERNAL */);});
},
_1st/* tinkerDiagSvgManager3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_manager"));
}),
_1su/* tinkerDiagSvgManager2 */ = function(_/* EXTERNAL */){
  var _1sv/* s4Nu */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lB/* DiagramDecorator.tinkerDiagSvgManager4 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1sw/* s4Nx */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1sx/* s4NA */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1sy/* s4ND */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lx/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */)),
  _1sz/* s4NG */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lw/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lv/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1st/* DiagramDecorator.tinkerDiagSvgManager3 */, _/* EXTERNAL */);});
},
_1sA/* tinkerDiagSvgManager1 */ = function(_1sB/* s4NJ */, _/* EXTERNAL */){
  return new F(function(){return _1su/* DiagramDecorator.tinkerDiagSvgManager2 */(_/* EXTERNAL */);});
},
_1sC/* tinkerDiagSvgPrimary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_4"));
}),
_1sD/* tinkerDiagSvgPrimary4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_2_3"));
}),
_1sE/* tinkerDiagSvgPrimary5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_secondary"));
}),
_1sF/* tinkerDiagSvgPrimary6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_2"));
}),
_1sG/* tinkerDiagSvgPrimary7 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_primary"));
}),
_1sH/* tinkerDiagSvgPrimary2 */ = function(_/* EXTERNAL */){
  var _1sI/* s4Mk */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1sG/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */)),
  _1sJ/* s4Mn */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sF/* DiagramDecorator.tinkerDiagSvgPrimary6 */, _1sE/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1sK/* s4Mq */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sD/* DiagramDecorator.tinkerDiagSvgPrimary4 */, _1sG/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sC/* DiagramDecorator.tinkerDiagSvgPrimary3 */, _1sG/* DiagramDecorator.tinkerDiagSvgPrimary7 */, _/* EXTERNAL */);});
},
_1sL/* tinkerDiagSvgPrimary1 */ = function(_1sM/* s4Mt */, _/* EXTERNAL */){
  return new F(function(){return _1sH/* DiagramDecorator.tinkerDiagSvgPrimary2 */(_/* EXTERNAL */);});
},
_1sN/* tinkerDiagSvgProducer3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_producer"));
}),
_1sO/* tinkerDiagSvgProducer2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lB/* DiagramDecorator.tinkerDiagSvgManager4 */, _1sN/* DiagramDecorator.tinkerDiagSvgProducer3 */, _/* EXTERNAL */);});
},
_1sP/* tinkerDiagSvgProducer1 */ = function(_1sQ/* s4M5 */, _/* EXTERNAL */){
  return new F(function(){return _1sO/* DiagramDecorator.tinkerDiagSvgProducer2 */(_/* EXTERNAL */);});
},
_1sR/* tinkerDiagSvgPublic3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_public"));
}),
_1sS/* tinkerDiagSvgPublic4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_H_3"));
}),
_1sT/* tinkerDiagSvgPublic2 */ = function(_/* EXTERNAL */){
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sS/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1sR/* DiagramDecorator.tinkerDiagSvgPublic3 */, _/* EXTERNAL */);});
},
_1sU/* tinkerDiagSvgPublic1 */ = function(_1sV/* s4M4 */, _/* EXTERNAL */){
  return new F(function(){return _1sT/* DiagramDecorator.tinkerDiagSvgPublic2 */(_/* EXTERNAL */);});
},
_1sW/* tinkerDiagSvgRaw3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("box_4_3"));
}),
_1sX/* tinkerDiagSvgRaw4 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_4"));
}),
_1sY/* tinkerDiagSvgRaw5 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_1_2"));
}),
_1sZ/* tinkerDiagSvgRaw6 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_raw"));
}),
_1t0/* tinkerDiagSvgRaw2 */ = function(_/* EXTERNAL */){
  var _1t1/* s4M9 */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lB/* DiagramDecorator.tinkerDiagSvgManager4 */, _1sZ/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1t2/* s4Mc */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sY/* DiagramDecorator.tinkerDiagSvgRaw5 */, _1sZ/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */)),
  _1t3/* s4Mf */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sX/* DiagramDecorator.tinkerDiagSvgRaw4 */, _1sZ/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sW/* DiagramDecorator.tinkerDiagSvgRaw3 */, _1sZ/* DiagramDecorator.tinkerDiagSvgRaw6 */, _/* EXTERNAL */);});
},
_1t4/* tinkerDiagSvgRaw1 */ = function(_1t5/* s4Mi */, _/* EXTERNAL */){
  return new F(function(){return _1t0/* DiagramDecorator.tinkerDiagSvgRaw2 */(_/* EXTERNAL */);});
},
_1t6/* tinkerDiagSvgSecondary3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("arrow_3_4"));
}),
_1t7/* tinkerDiagSvgSecondary2 */ = function(_/* EXTERNAL */){
  var _1t8/* s4Mv */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lu/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1sE/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1t9/* s4My */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1sE/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */)),
  _1ta/* s4MB */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1sS/* DiagramDecorator.tinkerDiagSvgPublic4 */, _1sE/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1t6/* DiagramDecorator.tinkerDiagSvgSecondary3 */, _1sE/* DiagramDecorator.tinkerDiagSvgPrimary5 */, _/* EXTERNAL */);});
},
_1tb/* tinkerDiagSvgSecondary1 */ = function(_1tc/* s4ME */, _/* EXTERNAL */){
  return new F(function(){return _1t7/* DiagramDecorator.tinkerDiagSvgSecondary2 */(_/* EXTERNAL */);});
},
_1td/* tinkerDiagSvgSteward3 */ = new T(function(){
  return B(unCStr/* EXTERNAL */("svg_steward"));
}),
_1te/* tinkerDiagSvgSteward2 */ = function(_/* EXTERNAL */){
  var _1tf/* s4Na */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lB/* DiagramDecorator.tinkerDiagSvgManager4 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1tg/* s4Nd */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lz/* DiagramDecorator.tinkerDiagSvgCurator8 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1th/* s4Ng */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lu/* DiagramDecorator.tinkerDiagSvgConsumer4 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1ti/* s4Nj */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1ly/* DiagramDecorator.tinkerDiagSvgCurator6 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1tj/* s4Nm */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lx/* DiagramDecorator.tinkerDiagSvgCurator5 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */)),
  _1tk/* s4Np */ = B(_1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lw/* DiagramDecorator.tinkerDiagSvgCurator4 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */));
  return new F(function(){return _1kt/* DiagramDecorator.tinkerDiagSvgConsumer5 */(_1lv/* DiagramDecorator.tinkerDiagSvgCurator3 */, _1td/* DiagramDecorator.tinkerDiagSvgSteward3 */, _/* EXTERNAL */);});
},
_1tl/* tinkerDiagSvgSteward1 */ = function(_1tm/* s4Ns */, _/* EXTERNAL */){
  return new F(function(){return _1te/* DiagramDecorator.tinkerDiagSvgSteward2 */(_/* EXTERNAL */);});
},
_1tn/* main1 */ = function(_/* EXTERNAL */){
  var _1to/* silz */ = function(_/* EXTERNAL */){
    var _1tp/* sigj */ = function(_1tq/* sig4 */, _/* EXTERNAL */){
      return new F(function(){return _1rO/* Overlay.overlay1 */(new T(function(){
        var _1tr/* sig9 */ = String/* EXTERNAL */(E(_1tq/* sig4 */));
        return fromJSStr/* EXTERNAL */(_1tr/* sig9 */);
      }), _/* EXTERNAL */);});
    },
    _1ts/* sign */ = __createJSFunc/* EXTERNAL */(2, E(_1tp/* sigj */)),
    _1tt/* sigs */ = "(function(s,f){Haste[s] = f;})",
    _1tu/* sigw */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tv/* sigE */ = __app2/* EXTERNAL */(E(_1tu/* sigw */), "overlay", _1ts/* sign */),
    _1tw/* sigV */ = __createJSFunc/* EXTERNAL */(2, function(_1tx/* sigM */, _/* EXTERNAL */){
      var _1ty/* sigO */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_1qm/* Page.visionTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tz/* sigZ */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tA/* sih7 */ = __app2/* EXTERNAL */(E(_1tz/* sigZ */), "toVision", _1tw/* sigV */),
    _1tB/* siho */ = __createJSFunc/* EXTERNAL */(2, function(_1tC/* sihf */, _/* EXTERNAL */){
      var _1tD/* sihh */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_2N/* Page.actionTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tE/* sihs */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tF/* sihA */ = __app2/* EXTERNAL */(E(_1tE/* sihs */), "toAction", _1tB/* siho */),
    _1tG/* sihR */ = __createJSFunc/* EXTERNAL */(2, function(_1tH/* sihI */, _/* EXTERNAL */){
      var _1tI/* sihK */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_3Z/* Page.lifecycleTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tJ/* sihV */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tK/* sii3 */ = __app2/* EXTERNAL */(E(_1tJ/* sihV */), "toLifecycle", _1tG/* sihR */),
    _1tL/* siik */ = __createJSFunc/* EXTERNAL */(2, function(_1tM/* siib */, _/* EXTERNAL */){
      var _1tN/* siid */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_3R/* Page.dataTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tO/* siio */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tP/* siiw */ = __app2/* EXTERNAL */(E(_1tO/* siio */), "toData", _1tL/* siik */),
    _1tQ/* siiN */ = __createJSFunc/* EXTERNAL */(2, function(_1tR/* siiE */, _/* EXTERNAL */){
      var _1tS/* siiG */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_1qc/* Page.rolesTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tT/* siiR */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tU/* siiZ */ = __app2/* EXTERNAL */(E(_1tT/* siiR */), "toRoles", _1tQ/* siiN */),
    _1tV/* sijg */ = __createJSFunc/* EXTERNAL */(2, function(_1tW/* sij7 */, _/* EXTERNAL */){
      var _1tX/* sij9 */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_1pY/* Page.mQuestionnaireTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1tY/* sijk */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1tZ/* sijs */ = __app2/* EXTERNAL */(E(_1tY/* sijk */), "toMQuestionnaire", _1tV/* sijg */),
    _1u0/* sijJ */ = __createJSFunc/* EXTERNAL */(2, function(_1u1/* sijA */, _/* EXTERNAL */){
      var _1u2/* sijC */ = B(_LW/* FormEngine.FormElement.Tabs.toTab1 */(_1q4/* Page.tQuestionnaireTab */, _1qn/* Page.pageTabGroup */, _/* EXTERNAL */));
      return _3e/* Haste.Prim.Any.jsNull */;
    }),
    _1u3/* sijN */ = eval/* EXTERNAL */(_1tt/* sigs */),
    _1u4/* sijV */ = __app2/* EXTERNAL */(E(_1u3/* sijN */), "toTQuestionnaire", _1u0/* sijJ */),
    _1u5/* sijY */ = B(_7v/* FormEngine.JQuery.select1 */(_1rq/* Main.lvl26 */, _/* EXTERNAL */)),
    _1u6/* sik1 */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1t4/* DiagramDecorator.tinkerDiagSvgRaw1 */, _1u5/* sijY */, _/* EXTERNAL */)),
    _1u7/* sik4 */ = B(_7v/* FormEngine.JQuery.select1 */(_1rp/* Main.lvl25 */, _/* EXTERNAL */)),
    _1u8/* sik7 */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sL/* DiagramDecorator.tinkerDiagSvgPrimary1 */, _1u7/* sik4 */, _/* EXTERNAL */)),
    _1u9/* sika */ = B(_7v/* FormEngine.JQuery.select1 */(_1ro/* Main.lvl24 */, _/* EXTERNAL */)),
    _1ua/* sikd */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1tb/* DiagramDecorator.tinkerDiagSvgSecondary1 */, _1u9/* sika */, _/* EXTERNAL */)),
    _1ub/* sikg */ = B(_7v/* FormEngine.JQuery.select1 */(_1rn/* Main.lvl23 */, _/* EXTERNAL */)),
    _1uc/* sikj */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sU/* DiagramDecorator.tinkerDiagSvgPublic1 */, _1ub/* sikg */, _/* EXTERNAL */)),
    _1ud/* sikm */ = B(_7v/* FormEngine.JQuery.select1 */(_1rm/* Main.lvl22 */, _/* EXTERNAL */)),
    _1ue/* sikp */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sP/* DiagramDecorator.tinkerDiagSvgProducer1 */, _1ud/* sikm */, _/* EXTERNAL */)),
    _1uf/* siks */ = B(_7v/* FormEngine.JQuery.select1 */(_1rl/* Main.lvl21 */, _/* EXTERNAL */)),
    _1ug/* sikv */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sn/* DiagramDecorator.tinkerDiagSvgExpert1 */, _1uf/* siks */, _/* EXTERNAL */)),
    _1uh/* siky */ = B(_7v/* FormEngine.JQuery.select1 */(_1rk/* Main.lvl20 */, _/* EXTERNAL */)),
    _1ui/* sikB */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1s3/* DiagramDecorator.tinkerDiagSvgConsumer1 */, _1uh/* siky */, _/* EXTERNAL */)),
    _1uj/* sikE */ = B(_7v/* FormEngine.JQuery.select1 */(_1rj/* Main.lvl19 */, _/* EXTERNAL */)),
    _1uk/* sikH */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sc/* DiagramDecorator.tinkerDiagSvgCurator1 */, _1uj/* sikE */, _/* EXTERNAL */)),
    _1ul/* sikK */ = B(_7v/* FormEngine.JQuery.select1 */(_1ri/* Main.lvl18 */, _/* EXTERNAL */)),
    _1um/* sikN */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1si/* DiagramDecorator.tinkerDiagSvgCustodian1 */, _1ul/* sikK */, _/* EXTERNAL */)),
    _1un/* sikQ */ = B(_7v/* FormEngine.JQuery.select1 */(_1rh/* Main.lvl17 */, _/* EXTERNAL */)),
    _1uo/* sikT */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1tl/* DiagramDecorator.tinkerDiagSvgSteward1 */, _1un/* sikQ */, _/* EXTERNAL */)),
    _1up/* sikW */ = B(_7v/* FormEngine.JQuery.select1 */(_1rg/* Main.lvl16 */, _/* EXTERNAL */)),
    _1uq/* sikZ */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sA/* DiagramDecorator.tinkerDiagSvgManager1 */, _1up/* sikW */, _/* EXTERNAL */)),
    _1ur/* sil2 */ = B(_7v/* FormEngine.JQuery.select1 */(_1rf/* Main.lvl15 */, _/* EXTERNAL */)),
    _1us/* sil5 */ = B(_Nn/* FormEngine.JQuery.onLoad1 */(_1sr/* DiagramDecorator.tinkerDiagSvgInvestigator1 */, _1ur/* sil2 */, _/* EXTERNAL */)),
    _1ut/* sil8 */ = B(_7v/* FormEngine.JQuery.select1 */(_3T/* Main.getRespondentKey2 */, _/* EXTERNAL */)),
    _1uu/* silg */ = __app1/* EXTERNAL */(E(_3S/* FormEngine.JQuery.getRadioValue_f1 */), E(_1ut/* sil8 */)),
    _1uv/* silw */ = B(A(_3j/* Haste.Ajax.ajaxRequest */,[_2E/* Control.Monad.IO.Class.$fMonadIOIO */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _6/* Haste.Prim.JSType.$fJSTypeJSString */, _d/* Haste.Prim.JSType.$fJSType[] */, _2F/* Haste.Ajax.POST */, _40/* Main.lvl11 */, new T2(1,new T2(0,_41/* Main.lvl12 */,new T(function(){
      var _1uw/* silk */ = String/* EXTERNAL */(_1uu/* silg */);
      return toJSStr/* EXTERNAL */(fromJSStr/* EXTERNAL */(_1uw/* silk */));
    })),_I/* GHC.Types.[] */), _1qO/* Main.lvl14 */, _/* EXTERNAL */]));
    return _3e/* Haste.Prim.Any.jsNull */;
  },
  _1ux/* silD */ = __createJSFunc/* EXTERNAL */(0, E(_1to/* silz */)),
  _1uy/* silJ */ = __app1/* EXTERNAL */(E(_1s0/* FormEngine.JQuery.ready_f1 */), _1ux/* silD */);
  return new F(function(){return _1/* Haste.Prim.Any.$fFromAny()4 */(_/* EXTERNAL */);});
},
_1uz/* main */ = function(_/* EXTERNAL */){
  return new F(function(){return _1tn/* Main.main1 */(_/* EXTERNAL */);});
};

var hasteMain = function() {B(A(_1uz, [0]));};window.onload = hasteMain;