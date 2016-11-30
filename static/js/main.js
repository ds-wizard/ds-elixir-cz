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

var _0=function(_){return 0;},_1=function(_2){return E(_2);},_3=new T2(0,_1,function(_4){return new T1(1,_4);}),_5=function(_6){return fromJSStr(E(_6));},_7=function(_8){return new T1(1,new T(function(){return _5(_8);}));},_9=function(_a){return toJSStr(E(_a));},_b=function(_c,_d,_){var _e=B(A1(_c,_)),_f=B(A1(_d,_));return _e;},_g=function(_h,_i,_){var _j=B(A1(_h,_)),_k=B(A1(_i,_));return new T(function(){return B(A1(_j,_k));});},_l=function(_m,_n,_){var _o=B(A1(_n,_));return _m;},_p=function(_q,_r,_){var _s=B(A1(_r,_));return new T(function(){return B(A1(_q,_s));});},_t=function(_u,_){return _u;},_v=function(_w,_x,_){var _y=B(A1(_w,_));return C > 19 ? new F(function(){return A1(_x,_);}) : (++C,A1(_x,_));},_z=new T(function(){return unCStr("base");}),_A=new T(function(){return unCStr("GHC.IO.Exception");}),_B=new T(function(){return unCStr("IOException");}),_C=function(_D){return E(new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),new T5(0,new Long(4053623282,1685460941,true),new Long(3693590983,2507416641,true),_z,_A,_B),__Z,__Z));},_E=function(_F){return E(E(_F).a);},_G=function(_H,_I,_J){var _K=B(A1(_H,_)),_L=B(A1(_I,_)),_M=hs_eqWord64(_K.a,_L.a);if(!_M){return __Z;}else{var _N=hs_eqWord64(_K.b,_L.b);return (!_N)?__Z:new T1(1,_J);}},_O=new T(function(){return unCStr(": ");}),_P=new T(function(){return unCStr(")");}),_Q=new T(function(){return unCStr(" (");}),_R=function(_S,_T){var _U=E(_S);return (_U._==0)?E(_T):new T2(1,_U.a,new T(function(){return _R(_U.b,_T);}));},_V=new T(function(){return unCStr("interrupted");}),_W=new T(function(){return unCStr("system error");}),_X=new T(function(){return unCStr("unsatisified constraints");}),_Y=new T(function(){return unCStr("user error");}),_Z=new T(function(){return unCStr("permission denied");}),_10=new T(function(){return unCStr("illegal operation");}),_11=new T(function(){return unCStr("end of file");}),_12=new T(function(){return unCStr("resource exhausted");}),_13=new T(function(){return unCStr("resource busy");}),_14=new T(function(){return unCStr("does not exist");}),_15=new T(function(){return unCStr("already exists");}),_16=new T(function(){return unCStr("resource vanished");}),_17=new T(function(){return unCStr("timeout");}),_18=new T(function(){return unCStr("unsupported operation");}),_19=new T(function(){return unCStr("hardware fault");}),_1a=new T(function(){return unCStr("inappropriate type");}),_1b=new T(function(){return unCStr("invalid argument");}),_1c=new T(function(){return unCStr("failed");}),_1d=new T(function(){return unCStr("protocol error");}),_1e=function(_1f,_1g){switch(E(_1f)){case 0:return _R(_15,_1g);case 1:return _R(_14,_1g);case 2:return _R(_13,_1g);case 3:return _R(_12,_1g);case 4:return _R(_11,_1g);case 5:return _R(_10,_1g);case 6:return _R(_Z,_1g);case 7:return _R(_Y,_1g);case 8:return _R(_X,_1g);case 9:return _R(_W,_1g);case 10:return _R(_1d,_1g);case 11:return _R(_1c,_1g);case 12:return _R(_1b,_1g);case 13:return _R(_1a,_1g);case 14:return _R(_19,_1g);case 15:return _R(_18,_1g);case 16:return _R(_17,_1g);case 17:return _R(_16,_1g);default:return _R(_V,_1g);}},_1h=new T(function(){return unCStr("}");}),_1i=new T(function(){return unCStr("{handle: ");}),_1j=function(_1k,_1l,_1m,_1n,_1o,_1p){var _1q=new T(function(){var _1r=new T(function(){var _1s=new T(function(){var _1t=E(_1n);if(!_1t._){return E(_1p);}else{var _1u=new T(function(){return _R(_1t,new T(function(){return _R(_P,_1p);},1));},1);return _R(_Q,_1u);}},1);return _1e(_1l,_1s);}),_1v=E(_1m);if(!_1v._){return E(_1r);}else{return _R(_1v,new T(function(){return _R(_O,_1r);},1));}}),_1w=E(_1o);if(!_1w._){var _1x=E(_1k);if(!_1x._){return E(_1q);}else{var _1y=E(_1x.a);if(!_1y._){var _1z=new T(function(){var _1A=new T(function(){return _R(_1h,new T(function(){return _R(_O,_1q);},1));},1);return _R(_1y.a,_1A);},1);return _R(_1i,_1z);}else{var _1B=new T(function(){var _1C=new T(function(){return _R(_1h,new T(function(){return _R(_O,_1q);},1));},1);return _R(_1y.a,_1C);},1);return _R(_1i,_1B);}}}else{return _R(_1w.a,new T(function(){return _R(_O,_1q);},1));}},_1D=function(_1E){var _1F=E(_1E);return _1j(_1F.a,_1F.b,_1F.c,_1F.d,_1F.f,__Z);},_1G=function(_1H,_1I){var _1J=E(_1H);return _1j(_1J.a,_1J.b,_1J.c,_1J.d,_1J.f,_1I);},_1K=function(_1L,_1M,_1N){var _1O=E(_1M);if(!_1O._){return unAppCStr("[]",_1N);}else{var _1P=new T(function(){var _1Q=new T(function(){var _1R=function(_1S){var _1T=E(_1S);if(!_1T._){return E(new T2(1,93,_1N));}else{var _1U=new T(function(){return B(A2(_1L,_1T.a,new T(function(){return _1R(_1T.b);})));});return new T2(1,44,_1U);}};return _1R(_1O.b);});return B(A2(_1L,_1O.a,_1Q));});return new T2(1,91,_1P);}},_1V=new T(function(){return new T5(0,_C,new T3(0,function(_1W,_1X,_1Y){var _1Z=E(_1X);return _1j(_1Z.a,_1Z.b,_1Z.c,_1Z.d,_1Z.f,_1Y);},_1D,function(_20,_21){return _1K(_1G,_20,_21);}),function(_22){return new T2(0,_1V,_22);},function(_23){var _24=E(_23);return _G(_E(_24.a),_C,_24.b);},_1D);}),_25=new T(function(){return E(_1V);}),_26=function(_27){return E(E(_27).c);},_28=function(_29){return new T6(0,__Z,7,__Z,_29,__Z,__Z);},_2a=function(_2b,_){var _2c=new T(function(){return B(A2(_26,_25,new T(function(){return B(A1(_28,_2b));})));});return die(_2c);},_2d=function(_2e,_){return _2a(_2e,_);},_2f=function(_2g){return C > 19 ? new F(function(){return A1(_2d,_2g);}) : (++C,A1(_2d,_2g));},_2h=function(_2i,_2j,_){var _2k=B(A1(_2i,_));return C > 19 ? new F(function(){return A2(_2j,_2k,_);}) : (++C,A2(_2j,_2k,_));},_2l=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,200,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_2m=function(_2n,_2o){var _2p=E(_2o);return (_2p._==0)?__Z:new T2(1,new T(function(){return B(A1(_2n,_2p.a));}),new T(function(){return _2m(_2n,_2p.b);}));},_2q=function(_2r){return E(E(_2r).a);},_2s=function(_2t,_2u,_2v){var _2w=function(_2x){var _2y=E(_2x);return jsCat(new T2(1,new T(function(){return B(A2(_2q,_2t,_2y.a));}),new T2(1,new T(function(){return B(A2(_2q,_2u,_2y.b));}),__Z)),"=");},_2z=jsCat(_2m(_2w,_2v),"&");return E(_2z);},_2A=(function(method, url, async, postdata, cb) {var xhr = new XMLHttpRequest();xhr.open(method, url, async);if(method == 'POST') {xhr.setRequestHeader('Content-type','application/x-www-form-urlencoded');}xhr.onreadystatechange = function() {if(xhr.readyState == 4) {cb(xhr.status == 200 ? xhr.responseText : null);}};xhr.send(postdata);}),_2B=function(_2C){return E(E(_2C).b);},_2D=new T(function(){var _2E=function(_){return __jsNull();},_2F=B(A1(_2E,_));return E(_2F);}),_2G=function(_2H){return E(E(_2H).b);},_2I=new T(function(){return toJSStr(__Z);}),_2J=function(_2K,_2L,_2M,_2N,_2O,_2P,_2Q,_2R){var _2S=new T(function(){return _2s(_2L,_2M,_2Q);}),_2T=new T(function(){return _9(_2P);}),_2U=function(_){var _2V=function(_2W){var _2X=function(_2Y){var _2Z=function(_30){var _31=new T(function(){return _2B(_2N);}),_32=function(_33,_){var _34=new T(function(){var _35=E(_33),_36=__eq(_35,E(_2D));if(!E(_36)){return B(A1(_31,new T(function(){return String(_35);})));}else{return __Z;}}),_37=B(A2(_2R,_34,_));return _2D;},_38=__createJSFunc(2,_32),_39=_2A(_2W,_2Y,true,_30,_38);return 0;};if(!E(_2O)){return _2Z(E(_2I));}else{var _3a=E(_2Q);if(!_3a._){return _2Z(E(_2I));}else{return _2Z(_2s(_2L,_2M,_3a));}}};if(!E(_2O)){if(!E(_2Q)._){return _2X(toJSStr(E(_2P)));}else{var _3b=jsCat(new T2(1,_2T,new T2(1,_2S,__Z)),"?");return _2X(_3b);}}else{return _2X(toJSStr(E(_2P)));}};if(!E(_2O)){return _2V("GET");}else{return _2V("POST");}};return C > 19 ? new F(function(){return A2(_2G,_2K,_2U);}) : (++C,A2(_2G,_2K,_2U));},_3c=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,400,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_3d=new T(function(){return (function (jq) { return jq.val(); });}),_3e=new T(function(){return unCStr("#respondent_key_field");}),_3f=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,300,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_3g=new T(function(){return unCStr("api/getData");}),_3h=function(_3i,_3j,_3k,_){var _3l=(function (key, val, jq) { jq.css(key, val); return jq; });return _3l(toJSStr(E(_3i)),toJSStr(E(_3j)),_3k);},_3m=function(_3n,_3o){var _3p=jsShowI(_3n);return _R(fromJSStr(_3p),_3o);},_3q=function(_3r,_3s,_3t){if(_3s>=0){return _3m(_3s,_3t);}else{if(_3r<=6){return _3m(_3s,_3t);}else{return new T2(1,40,new T(function(){var _3u=jsShowI(_3s);return _R(fromJSStr(_3u),new T2(1,41,_3t));}));}}},_3v=new T(function(){return unCStr("px");}),_3w=function(_3x){return _R(_3q(0,_3x,__Z),_3v);},_3y=new T(function(){return unCStr("_desc-subpane");}),_3z=function(_3A){while(1){var _3B=E(_3A);switch(_3B._){case 0:return _3B;case 1:_3A=_3B.c;continue;case 2:_3A=_3B.c;continue;case 3:_3A=_3B.c;continue;case 4:_3A=_3B.d;continue;case 5:_3A=_3B.c;continue;case 6:_3A=_3B.c;continue;case 7:_3A=_3B.c;continue;case 8:_3A=_3B.d;continue;case 9:_3A=_3B.c;continue;case 10:_3A=_3B.b;continue;default:_3A=_3B.b;continue;}}},_3C=function(_3D){var _3E=E(_3D);switch(_3E._){case 0:return E(_3E.a);case 1:return E(_3E.a);case 2:return E(_3E.a);case 3:return E(_3E.a);case 4:return E(_3E.a);case 5:return E(_3E.a);case 6:return E(_3E.a);case 7:return E(_3E.a);case 8:return E(_3E.a);case 9:return E(_3E.a);case 10:return E(_3E.a);default:return E(_3E.a);}},_3F=function(_3G){var _3H=E(_3G);switch(_3H._){case 0:return E(_3H.a);case 1:return E(_3H.a);case 2:return E(_3H.a);case 3:return E(_3H.a);case 4:return E(_3H.a);case 5:return E(_3H.a);case 6:return E(_3H.a);case 7:return E(_3H.a);case 8:return E(_3H.a);case 9:return E(_3H.a);case 10:return E(_3H.a);default:return E(_3H.a);}},_3I=function(_3J){return _3q(0,E(_3J),__Z);},_3K=function(_3L,_3M){var _3N=E(_3L);if(!_3N._){return __Z;}else{var _3O=_3N.a,_3P=E(_3M);return (_3P==1)?new T2(1,new T(function(){return B(_3I(_3O));}),__Z):new T2(1,new T(function(){return B(_3I(_3O));}),new T(function(){return _3K(_3N.b,_3P-1|0);}));}},_3Q=function(_3R){var _3S=E(_3R);if(!_3S._){return __Z;}else{return _R(_3S.a,new T(function(){return _3Q(_3S.b);},1));}},_3T=new T(function(){return unCStr("_");}),_3U=function(_3V,_3W){var _3X=E(_3W);return (_3X._==0)?__Z:new T2(1,_3V,new T2(1,_3X.a,new T(function(){return _3U(_3V,_3X.b);})));},_3Y=function(_3Z){var _40=E(_3Z);if(!_40._){return __Z;}else{var _41=E(_40.b)+1|0;if(0>=_41){return __Z;}else{var _42=_3K(_40.a,_41);if(!_42._){return __Z;}else{return _3Q(new T2(1,_42.a,new T(function(){return _3U(_3T,_42.b);})));}}}},_43=function(_44){return _R(_3Y(_3C(_3F(_3z(_44))).b),_3y);},_45=new T(function(){return (function (jq) { return jq.scrollTop(); });}),_46=new T(function(){return (function (jq) { return jq.position().top; });}),_47=new T(function(){return (function () { return $(window); });}),_48=new T(function(){return (function (jq) { return jq.is(':visible'); });}),_49=new T(function(){return unCStr("margin-top");}),_4a=new T(function(){return unCStr("#");}),_4b=function(_4c,_){var _4d=(function (elId) { var res = $(elId); if (res.length === 0) { console.warn('empty $ selection ' + elId); }; return res; });return _4d(toJSStr(E(_4c)));},_4e=function(_4f,_){var _4g=E(_4f);if(!_4g._){return 0;}else{var _4h=_R(_4a,new T(function(){return _43(_4g.a);},1)),_4i=_4b(_4h,_),_4j=E(_48),_4k=_4j(E(_4i)),_4l=function(_4m,_){var _4n=E(_4m);if(!_4n._){return __Z;}else{var _4o=_R(_4a,new T(function(){return _43(_4n.a);},1)),_4p=_4b(_4o,_),_4q=_4j(E(_4p)),_4r=_4l(_4n.b,_);return new T(function(){if(!_4q){return E(_4r);}else{return new T2(1,_4o,_4r);}});}},_4s=_4l(_4g.b,_),_4t=function(_4u,_4v){var _4w=_4b(_4u,_),_4x=E(_47)(),_4y=E(_45)(_4x),_4z=E(_4w),_4A=E(_46)(_4z),_4B=Number(_4y),_4C=jsTrunc(_4B),_4D=Number(_4A),_4E=jsTrunc(_4D),_4F=_4C-_4E|0;if(_4F<=0){return 0;}else{var _4G=_3h(_49,_3w(_4F),_4z,_);return 0;}};if(!_4k){var _4H=E(_4s);if(!_4H._){return 0;}else{return _4t(_4H.a,_4H.b);}}else{return _4t(_4h,_4s);}}},_4I=function(_4J,_){var _4K=(function (jq) { jq.resize(); }),_4L=_4K(_4J);return _4J;},_4M=function(_4N){while(1){var _4O=(function(_4P){var _4Q=E(_4P);if(!_4Q._){return __Z;}else{var _4R=_4Q.b,_4S=E(_4Q.a);if(!_4S._){_4N=_4R;return __continue;}else{return new T2(1,_4S.a,new T(function(){return _4M(_4R);}));}}})(_4N);if(_4O!=__continue){return _4O;}}},_4T=function(_4U,_){var _4V=(function (s) { console.error(s); }),_4W=_4V(toJSStr(E(_4U)));return 0;},_4X=function(_4Y,_4Z,_50){while(1){var _51=(function(_52,_53,_54){var _55=E(_52);if(!_55._){return new T2(0,_53,_54);}else{var _56=_55.a,_57=new T(function(){return _R(_54,new T2(1,new T(function(){return E(_58(_53,_56).b);}),__Z));});_4Y=_55.b;_4Z=new T(function(){return E(_58(_53,_56).a);});_50=_57;return __continue;}})(_4Y,_4Z,_50);if(_51!=__continue){return _51;}}},_59=function(_5a,_5b,_5c){while(1){var _5d=(function(_5e,_5f,_5g){var _5h=E(_5e);if(!_5h._){return new T2(0,_5f,_5g);}else{var _5i=_5h.a,_5j=new T(function(){return _R(_5g,new T2(1,new T(function(){return E(_58(_5f,_5i).b);}),__Z));});_5a=_5h.b;_5b=new T(function(){return E(_58(_5f,_5i).a);});_5c=_5j;return __continue;}})(_5a,_5b,_5c);if(_5d!=__continue){return _5d;}}},_5k=function(_5l,_5m,_5n){while(1){var _5o=(function(_5p,_5q,_5r){var _5s=E(_5p);if(!_5s._){return new T2(0,_5q,_5r);}else{var _5t=_5s.a,_5u=new T(function(){return _R(_5r,new T2(1,new T(function(){return E(_58(_5q,_5t).b);}),__Z));});_5l=_5s.b;_5m=new T(function(){return E(_58(_5q,_5t).a);});_5n=_5u;return __continue;}})(_5l,_5m,_5n);if(_5o!=__continue){return _5o;}}},_5v=function(_5w,_5x,_5y){while(1){var _5z=(function(_5A,_5B,_5C){var _5D=E(_5A);if(!_5D._){return new T2(0,_5B,_5C);}else{var _5E=_5D.a,_5F=new T(function(){return _R(_5C,new T2(1,new T(function(){return E(_58(_5B,_5E).b);}),__Z));});_5w=_5D.b;_5x=new T(function(){return E(_58(_5B,_5E).a);});_5y=_5F;return __continue;}})(_5w,_5x,_5y);if(_5z!=__continue){return _5z;}}},_5G=function(_5H,_5I,_5J){while(1){var _5K=(function(_5L,_5M,_5N){var _5O=E(_5L);if(!_5O._){return new T2(0,_5M,_5N);}else{var _5P=_5O.a,_5Q=new T(function(){return _R(_5N,new T2(1,new T(function(){return E(_58(_5M,_5P).b);}),__Z));});_5H=_5O.b;_5I=new T(function(){return E(_58(_5M,_5P).a);});_5J=_5Q;return __continue;}})(_5H,_5I,_5J);if(_5K!=__continue){return _5K;}}},_5R=new T(function(){return unCStr("Prelude.");}),_5S=new T(function(){return err(new T(function(){return _R(_5R,new T(function(){return unCStr("!!: negative index");}));}));}),_5T=new T(function(){return err(new T(function(){return _R(_5R,new T(function(){return unCStr("!!: index too large");}));}));}),_5U=function(_5V,_5W){while(1){var _5X=E(_5V);if(!_5X._){return E(_5T);}else{var _5Y=E(_5W);if(!_5Y){return E(_5X.a);}else{_5V=_5X.b;_5W=_5Y-1|0;continue;}}}},_5Z=function(_60,_61){if(_61>=0){return _5U(_60,_61);}else{return E(_5S);}},_62=new T(function(){return new T2(1,0,_62);}),_63=function(_64){var _65=E(_64);if(!_65._){return __Z;}else{var _66=_65.a,_67=_65.b,_68=new T(function(){var _69=E(_67),_6a=new T2(1,new T(function(){return _5Z(_66,_69)+1|0;}),_62);if(0>=_69){return E(_6a);}else{var _6b=function(_6c,_6d){var _6e=E(_6c);if(!_6e._){return E(_6a);}else{var _6f=_6e.a,_6g=E(_6d);return (_6g==1)?new T2(1,_6f,_6a):new T2(1,_6f,new T(function(){return _6b(_6e.b,_6g-1|0);}));}};return _6b(_66,_69);}});return new T2(1,_68,_67);}},_6h=function(_6i,_6j,_6k){while(1){var _6l=(function(_6m,_6n,_6o){var _6p=E(_6m);if(!_6p._){return new T2(0,_6n,_6o);}else{var _6q=_6p.b,_6r=E(_6p.a);if(!_6r._){var _6s=_6n;_6i=_6q;_6j=_6s;_6k=new T(function(){return _R(_6o,new T2(1,_6r,__Z));});return __continue;}else{var _6t=new T(function(){var _6u=new T(function(){var _6v=new T(function(){var _6w=E(_6n);if(!_6w._){return __Z;}else{return new T2(1,_6w.a,new T(function(){return E(_6w.b)+1|0;}));}});return E(_5G(_6r.c,_6v,__Z).b);});return _R(_6o,new T2(1,new T3(1,_6n,_6r.b,_6u),__Z));});_6i=_6q;_6j=new T(function(){return _63(_6n);});_6k=_6t;return __continue;}}})(_6i,_6j,_6k);if(_6l!=__continue){return _6l;}}},_58=function(_6x,_6y){var _6z=E(_6y);switch(_6z._){case 0:return new T2(0,new T(function(){return _63(_6x);}),new T1(0,new T(function(){var _6A=E(_6z.a);return {_:0,a:_6A.a,b:_6x,c:_6A.c,d:_6A.d,e:_6A.e,f:_6A.f,g:_6A.g,h:_6A.h,i:_6A.i};})));case 1:return new T2(0,new T(function(){return _63(_6x);}),new T1(1,new T(function(){var _6B=E(_6z.a);return {_:0,a:_6B.a,b:_6x,c:_6B.c,d:_6B.d,e:_6B.e,f:_6B.f,g:_6B.g,h:_6B.h,i:_6B.i};})));case 2:return new T2(0,new T(function(){return _63(_6x);}),new T1(2,new T(function(){var _6C=E(_6z.a);return {_:0,a:_6C.a,b:_6x,c:_6C.c,d:_6C.d,e:_6C.e,f:_6C.f,g:_6C.g,h:_6C.h,i:_6C.i};})));case 3:return new T2(0,new T(function(){return _63(_6x);}),new T2(3,new T(function(){var _6D=E(_6z.a);return {_:0,a:_6D.a,b:_6x,c:_6D.c,d:_6D.d,e:_6D.e,f:_6D.f,g:_6D.g,h:_6D.h,i:_6D.i};}),_6z.b));case 4:var _6E=new T(function(){var _6F=new T(function(){var _6G=E(_6x);if(!_6G._){return __Z;}else{return new T2(1,_6G.a,new T(function(){return E(_6G.b)+1|0;}));}});return E(_6h(_6z.b,_6F,__Z).b);});return new T2(0,new T(function(){return _63(_6x);}),new T2(4,new T(function(){var _6H=E(_6z.a);return {_:0,a:_6H.a,b:_6x,c:_6H.c,d:_6H.d,e:_6H.e,f:_6H.f,g:_6H.g,h:_6H.h,i:_6H.i};}),_6E));case 5:return new T2(0,new T(function(){return _63(_6x);}),new T2(5,new T(function(){var _6I=E(_6z.a);return {_:0,a:_6I.a,b:_6x,c:_6I.c,d:_6I.d,e:_6I.e,f:_6I.f,g:_6I.g,h:_6I.h,i:_6I.i};}),_6z.b));case 6:var _6J=new T(function(){var _6K=new T(function(){var _6L=E(_6x);if(!_6L._){return __Z;}else{return new T2(1,_6L.a,new T(function(){return E(_6L.b)+1|0;}));}});return E(_5v(_6z.b,_6K,__Z).b);});return new T2(0,new T(function(){return _63(_6x);}),new T2(6,new T(function(){var _6M=E(_6z.a);return {_:0,a:_6M.a,b:_6x,c:_6M.c,d:_6M.d,e:_6M.e,f:_6M.f,g:_6M.g,h:_6M.h,i:_6M.i};}),_6J));case 7:var _6N=new T(function(){var _6O=new T(function(){var _6P=E(_6x);if(!_6P._){return __Z;}else{return new T2(1,_6P.a,new T(function(){return E(_6P.b)+1|0;}));}});return E(_5k(_6z.c,_6O,__Z).b);});return new T2(0,new T(function(){return _63(_6x);}),new T3(7,new T(function(){var _6Q=E(_6z.a);return {_:0,a:_6Q.a,b:_6x,c:_6Q.c,d:_6Q.d,e:_6Q.e,f:_6Q.f,g:_6Q.g,h:_6Q.h,i:_6Q.i};}),new T(function(){var _6R=E(_6x);if(!_6R._){return 0;}else{return E(_6R.b);}}),_6N));case 8:var _6S=new T(function(){var _6T=new T(function(){var _6U=E(_6x);if(!_6U._){return __Z;}else{return new T2(1,_6U.a,new T(function(){return E(_6U.b)+1|0;}));}});return E(_59(_6z.c,_6T,__Z).b);});return new T2(0,new T(function(){return _63(_6x);}),new T3(8,new T(function(){var _6V=E(_6z.a);return {_:0,a:_6V.a,b:_6x,c:_6V.c,d:_6V.d,e:_6V.e,f:_6V.f,g:_6V.g,h:_6V.h,i:_6V.i};}),new T(function(){var _6W=E(_6x);if(!_6W._){return 0;}else{return E(_6W.b);}}),_6S));case 9:var _6X=new T(function(){var _6Y=new T(function(){var _6Z=E(_6x);if(!_6Z._){return __Z;}else{return new T2(1,_6Z.a,new T(function(){return E(_6Z.b)+1|0;}));}});return E(_4X(_6z.c,_6Y,__Z).b);});return new T2(0,new T(function(){return _63(_6x);}),new T3(9,new T(function(){var _70=E(_6z.a);return {_:0,a:_70.a,b:_6x,c:_70.c,d:_70.d,e:_70.e,f:_70.f,g:_70.g,h:_70.h,i:_70.i};}),new T(function(){var _71=E(_6x);if(!_71._){return 0;}else{return E(_71.b);}}),_6X));case 10:return new T2(0,_6x,_6z);default:return new T2(0,_6x,_6z);}},_72=function(_73,_74,_75){while(1){var _76=(function(_77,_78,_79){var _7a=E(_77);if(!_7a._){return new T2(0,_78,_79);}else{var _7b=_7a.a,_7c=new T(function(){return _R(_79,new T2(1,new T(function(){return E(_58(_78,_7b).b);}),__Z));});_73=_7a.b;_74=new T(function(){return E(_58(_78,_7b).a);});_75=_7c;return __continue;}})(_73,_74,_75);if(_76!=__continue){return _76;}}},_7d=new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Other");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T1(1,{_:0,a:new T1(1,new T(function(){return unCStr("Your comments");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z}),__Z)),_7e=new T1(0,new T(function(){return unCStr("thousand EUR");})),_7f=new T0(3),_7g=new T(function(){return unCStr("raw-cost-sum");}),_7h=new T(function(){return unCStr("TB");}),_7i=new T2(1,new T2(1,new T(function(){return unCStr("raw-volume-genomics");}),new T2(1,new T(function(){return unCStr("raw-volume-proteomics");}),new T2(1,new T(function(){return unCStr("raw-volume-others");}),new T2(1,new T(function(){return unCStr("prim-volume");}),new T2(1,new T(function(){return unCStr("sec-volume");}),__Z))))),new T(function(){return unCStr("total-volume");})),_7j=new T(function(){return unCStr("raw-volume-sum");}),_7k=new T(function(){return unCStr("raw-cost-others");}),_7l=new T(function(){return unCStr("raw-cost-proteomics");}),_7m=new T(function(){return unCStr("raw-cost-genomics");}),_7n=new T2(1,new T2(0,new T2(1,_7m,new T2(1,_7l,new T2(1,_7k,__Z))),_7g),__Z),_7o=new T1(1,new T(function(){return unCStr("Rough estimation of FTEs + investments + consumables");})),_7p=new T1(1,new T(function(){return unCStr("Cost for year 2015");})),_7q=new T1(1,new T2(1,new T(function(){return unCStr("MB");}),new T2(1,new T(function(){return unCStr("GB");}),new T2(1,_7h,new T2(1,new T(function(){return unCStr("PB");}),__Z))))),_7r=new T2(1,new T(function(){return unCStr("arrow_1_2");}),new T2(1,new T(function(){return unCStr("arrow_1_4");}),__Z)),_7s=new T(function(){return unCStr("raw-volume-others");}),_7t=new T1(1,new T(function(){return unCStr("Volume");})),_7u=new T(function(){return unCStr("raw-volume-proteomics");}),_7v=new T(function(){return unCStr("raw-volume-genomics");}),_7w=new T2(1,new T2(1,new T2(1,_7v,new T2(1,_7u,new T2(1,_7s,__Z))),_7j),new T2(1,new T2(2,_7j,new T(function(){return unCStr("prim-raw-volume");})),__Z)),_7x=new T1(0,new T(function(){return unCStr("%");})),_7y=new T2(1,_7f,new T2(1,new T1(4,function(_7z){return (E(_7z)==100)?true:false;}),__Z)),_7A=new T(function(){return unCStr("raw-accessibility-sum");}),_7B=new T1(1,new T(function(){return unCStr("Sum");})),_7C=new T2(1,new T1(4,function(_7D){var _7E=E(_7D);return (_7E<0)?false:_7E<=100;}),__Z),_7F=new T(function(){return unCStr("raw-accessibility-open");}),_7G=new T(function(){return unCStr("raw-accessibility-closed");}),_7H=new T(function(){return unCStr("raw-accessibility-inside");}),_7I=new T2(1,new T2(0,new T2(1,_7H,new T2(1,_7G,new T2(1,_7F,__Z))),_7A),_7C),_7J=new T(function(){return unCStr("box_5_e");}),_7K=new T(function(){return unCStr("raw-funding-institutional");}),_7L=new T(function(){return unCStr("raw-funding-sum");}),_7M=new T(function(){return unCStr("raw-funding-worldwide");}),_7N=new T(function(){return unCStr("raw-funding-european");}),_7O=new T(function(){return unCStr("raw-funding-national");}),_7P=new T2(1,new T2(0,new T2(1,_7K,new T2(1,_7O,new T2(1,_7N,new T2(1,_7M,__Z)))),_7L),_7C),_7Q=new T2(1,new T1(0,new T(function(){return unCStr("No");})),__Z),_7R=new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("For year 2015");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T1(0,new T(function(){return unCStr("thousand EUR");}))),_7S={_:0,a:new T1(1,new T(function(){return unCStr("Funding");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},_7T=new T1(0,new T(function(){return unCStr("%");})),_7U=new T(function(){return unCStr("prim-external-internal-funding-sum");}),_7V=new T2(1,_7f,new T2(1,new T1(4,function(_7W){return (E(_7W)==100)?true:false;}),__Z)),_7X=new T1(1,new T(function(){return unCStr("Sum");})),_7Y=new T1(1,new T(function(){return unCStr("World-wide");})),_7Z=new T2(1,new T1(4,function(_80){var _81=E(_80);return (_81<0)?false:_81<=100;}),__Z),_82=new T(function(){return unCStr("prim-external-internal-funding-worldwide");}),_83=new T(function(){return unCStr("prim-external-internal-funding-european");}),_84=new T(function(){return unCStr("prim-external-internal-funding-national");}),_85=new T(function(){return unCStr("prim-external-internal-funding-institutional");}),_86=new T2(1,new T2(0,new T2(1,_85,new T2(1,_84,new T2(1,_83,new T2(1,_82,__Z)))),_7U),_7Z),_87=new T1(1,new T(function(){return unCStr("European");})),_88=new T1(1,new T(function(){return unCStr("National");})),_89=new T1(1,new T(function(){return unCStr("Institutional");})),_8a=new T(function(){return unCStr("TB");}),_8b=new T1(1,new T2(1,new T(function(){return unCStr("MB");}),new T2(1,new T(function(){return unCStr("GB");}),new T2(1,_8a,new T2(1,new T(function(){return unCStr("PB");}),__Z))))),_8c=new T(function(){return unCStr("prim-internal-funding-sum");}),_8d=new T(function(){return unCStr("prim-internal-funding-worldwide");}),_8e=new T(function(){return unCStr("prim-internal-funding-european");}),_8f=new T(function(){return unCStr("prim-internal-funding-national");}),_8g=new T(function(){return unCStr("prim-internal-funding-institutional");}),_8h=new T2(1,new T2(0,new T2(1,_8g,new T2(1,_8f,new T2(1,_8e,new T2(1,_8d,__Z)))),_8c),_7Z),_8i=new T(function(){return unCStr("prim-accessibility-sum");}),_8j=new T(function(){return unCStr("prim-accessibility-open");}),_8k=new T(function(){return unCStr("prim-accessibility-closed");}),_8l=new T(function(){return unCStr("prim-accessibility-inside");}),_8m=new T2(1,new T2(0,new T2(1,_8l,new T2(1,_8k,new T2(1,_8j,__Z))),_8i),_7Z),_8n=new T(function(){return unCStr("box_5_e");}),_8o=new T(function(){return unCStr("Yes");}),_8p=new T(function(){return unCStr("prim-volume");}),_8q=new T2(1,new T1(0,new T(function(){return unCStr("No");})),__Z),_8r=new T(function(){return unCStr("sec-internal-funding-sum");}),_8s=new T2(1,_7f,new T2(1,new T1(4,function(_8t){return (E(_8t)==100)?true:false;}),__Z)),_8u=new T1(1,new T(function(){return unCStr("Sum");})),_8v=new T1(0,new T(function(){return unCStr("%");})),_8w=new T2(1,new T1(4,function(_8x){var _8y=E(_8x);return (_8y<0)?false:_8y<=100;}),__Z),_8z=new T(function(){return unCStr("sec-internal-funding-worldwide");}),_8A=new T(function(){return unCStr("sec-internal-funding-european");}),_8B=new T(function(){return unCStr("sec-internal-funding-national");}),_8C=new T(function(){return unCStr("sec-internal-funding-institutional");}),_8D=new T2(1,new T2(0,new T2(1,_8C,new T2(1,_8B,new T2(1,_8A,new T2(1,_8z,__Z)))),_8r),_8w),_8E=new T1(1,new T(function(){return unCStr("World-wide");})),_8F=new T1(1,new T(function(){return unCStr("European");})),_8G=new T1(1,new T(function(){return unCStr("National");})),_8H=new T1(1,new T(function(){return unCStr("Institutional");})),_8I={_:0,a:new T1(1,new T(function(){return unCStr("Funding");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},_8J=new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("For year 2015");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T1(0,new T(function(){return unCStr("thousand EUR");}))),_8K=new T(function(){return unCStr("sec-accessibility-sum");}),_8L=new T(function(){return unCStr("sec-accessibility-open");}),_8M=new T(function(){return unCStr("sec-accessibility-closed");}),_8N=new T(function(){return unCStr("sec-accessibility-inside");}),_8O=new T2(1,new T2(0,new T2(1,_8N,new T2(1,_8M,new T2(1,_8L,__Z))),_8K),new T2(1,new T1(4,function(_8P){return E(_8P)<=100;}),__Z)),_8Q=new T(function(){return unCStr("box_5_e");}),_8R=new T(function(){return unCStr("Yes");}),_8S=new T(function(){return unCStr("TB");}),_8T=new T1(1,new T2(1,new T(function(){return unCStr("MB");}),new T2(1,new T(function(){return unCStr("GB");}),new T2(1,_8S,new T2(1,new T(function(){return unCStr("PB");}),__Z))))),_8U=new T(function(){return unCStr("sec-external-internal-funding-sum");}),_8V=new T(function(){return unCStr("sec-external-internal-funding-worldwide");}),_8W=new T(function(){return unCStr("sec-external-internal-funding-european");}),_8X=new T(function(){return unCStr("sec-external-internal-funding-national");}),_8Y=new T(function(){return unCStr("sec-external-internal-funding-institutional");}),_8Z=new T2(1,new T2(0,new T2(1,_8Y,new T2(1,_8X,new T2(1,_8W,new T2(1,_8V,__Z)))),_8U),_8w),_90=new T1(0,new T(function(){return unCStr("%");})),_91=new T(function(){return unCStr("storage-providers-sum");}),_92=new T(function(){return unCStr("storage-provider-external");}),_93=new T(function(){return unCStr("storage-provider-institutional");}),_94=new T(function(){return unCStr("storage-provider-group");}),_95=new T2(1,new T2(0,new T2(1,_94,new T2(1,_93,new T2(1,_92,__Z))),_91),new T2(1,new T1(4,function(_96){var _97=E(_96);return (_97<0)?false:_97<=100;}),__Z)),_98=new T(function(){return unCStr("TB");}),_99=new T1(1,new T2(1,new T(function(){return unCStr("MB");}),new T2(1,new T(function(){return unCStr("GB");}),new T2(1,_98,new T2(1,new T(function(){return unCStr("PB");}),__Z))))),_9a=new T1(0,new T(function(){return unCStr("years");})),_9b=new T2(1,new T1(0,new T(function(){return unCStr("no");})),new T2(1,new T1(0,new T(function(){return unCStr("yes");})),__Z)),_9c=new T1(0,new T(function(){return unCStr("Full-time equivalent");})),_9d=new T1(1,new T(function(){return unCStr("Haste[\'toRoles\']()");})),_9e=new T(function(){return unCStr("box_2");}),_9f=new T(function(){return unCStr("box_3");}),_9g=new T(function(){return unCStr("box_4_1");}),_9h=new T(function(){return unCStr("box_5_e");}),_9i=new T(function(){return unCStr("box_5_i");}),_9j=new T2(1,_9g,new T2(1,_9i,new T2(1,_9h,new T2(1,new T(function(){return unCStr("box_6");}),__Z)))),_9k=new T2(1,_9e,new T2(1,_9f,_9j)),_9l=new T(function(){return unCStr("box_1");}),_9m=new T(function(){return new T2(1,0,_9m);}),_9n=new T(function(){return E(_72(new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("0.General Info");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Registration of the responder");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T1(0,{_:0,a:new T1(1,new T(function(){return unCStr("First name");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z}),new T2(1,new T1(0,{_:0,a:new T1(1,new T(function(){return unCStr("Surname");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z}),new T2(1,new T1(2,{_:0,a:new T1(1,new T(function(){return unCStr("Email");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z}),__Z)))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Affiliation");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(5,{_:0,a:new T1(1,new T(function(){return unCStr("Country");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T2(0,__Z,new T(function(){return unCStr("--select--");})),new T2(1,new T2(0,new T(function(){return unCStr("AF");}),new T(function(){return unCStr("Afghanistan");})),new T2(1,new T2(0,new T(function(){return unCStr("AX");}),new T(function(){return unCStr("\u00c5land Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("AL");}),new T(function(){return unCStr("Albania");})),new T2(1,new T2(0,new T(function(){return unCStr("DZ");}),new T(function(){return unCStr("Algeria");})),new T2(1,new T2(0,new T(function(){return unCStr("AS");}),new T(function(){return unCStr("American Samoa");})),new T2(1,new T2(0,new T(function(){return unCStr("AD");}),new T(function(){return unCStr("Andorra");})),new T2(1,new T2(0,new T(function(){return unCStr("AO");}),new T(function(){return unCStr("Angola");})),new T2(1,new T2(0,new T(function(){return unCStr("AI");}),new T(function(){return unCStr("Anguilla");})),new T2(1,new T2(0,new T(function(){return unCStr("AQ");}),new T(function(){return unCStr("Antarctica");})),new T2(1,new T2(0,new T(function(){return unCStr("AG");}),new T(function(){return unCStr("Antigua and Barbuda");})),new T2(1,new T2(0,new T(function(){return unCStr("AR");}),new T(function(){return unCStr("Argentina");})),new T2(1,new T2(0,new T(function(){return unCStr("AM");}),new T(function(){return unCStr("Armenia");})),new T2(1,new T2(0,new T(function(){return unCStr("AW");}),new T(function(){return unCStr("Aruba");})),new T2(1,new T2(0,new T(function(){return unCStr("AU");}),new T(function(){return unCStr("Australia");})),new T2(1,new T2(0,new T(function(){return unCStr("AT");}),new T(function(){return unCStr("Austria");})),new T2(1,new T2(0,new T(function(){return unCStr("AZ");}),new T(function(){return unCStr("Azerbaijan");})),new T2(1,new T2(0,new T(function(){return unCStr("BS");}),new T(function(){return unCStr("Bahamas");})),new T2(1,new T2(0,new T(function(){return unCStr("BH");}),new T(function(){return unCStr("Bahrain");})),new T2(1,new T2(0,new T(function(){return unCStr("BD");}),new T(function(){return unCStr("Bangladesh");})),new T2(1,new T2(0,new T(function(){return unCStr("BB");}),new T(function(){return unCStr("Barbados");})),new T2(1,new T2(0,new T(function(){return unCStr("BY");}),new T(function(){return unCStr("Belarus");})),new T2(1,new T2(0,new T(function(){return unCStr("BE");}),new T(function(){return unCStr("Belgium");})),new T2(1,new T2(0,new T(function(){return unCStr("BZ");}),new T(function(){return unCStr("Belize");})),new T2(1,new T2(0,new T(function(){return unCStr("BJ");}),new T(function(){return unCStr("Benin");})),new T2(1,new T2(0,new T(function(){return unCStr("BM");}),new T(function(){return unCStr("Bermuda");})),new T2(1,new T2(0,new T(function(){return unCStr("BT");}),new T(function(){return unCStr("Bhutan");})),new T2(1,new T2(0,new T(function(){return unCStr("BO");}),new T(function(){return unCStr("Bolivia, Plurinational State of");})),new T2(1,new T2(0,new T(function(){return unCStr("BQ");}),new T(function(){return unCStr("Bonaire, Sint Eustatius and Saba");})),new T2(1,new T2(0,new T(function(){return unCStr("BA");}),new T(function(){return unCStr("Bosnia and Herzegovina");})),new T2(1,new T2(0,new T(function(){return unCStr("BW");}),new T(function(){return unCStr("Botswana");})),new T2(1,new T2(0,new T(function(){return unCStr("BV");}),new T(function(){return unCStr("Bouvet Island");})),new T2(1,new T2(0,new T(function(){return unCStr("BR");}),new T(function(){return unCStr("Brazil");})),new T2(1,new T2(0,new T(function(){return unCStr("IO");}),new T(function(){return unCStr("British Indian Ocean Territory");})),new T2(1,new T2(0,new T(function(){return unCStr("BN");}),new T(function(){return unCStr("Brunei Darussalam");})),new T2(1,new T2(0,new T(function(){return unCStr("BG");}),new T(function(){return unCStr("Bulgaria");})),new T2(1,new T2(0,new T(function(){return unCStr("BF");}),new T(function(){return unCStr("Burkina Faso");})),new T2(1,new T2(0,new T(function(){return unCStr("BI");}),new T(function(){return unCStr("Burundi");})),new T2(1,new T2(0,new T(function(){return unCStr("KH");}),new T(function(){return unCStr("Cambodia");})),new T2(1,new T2(0,new T(function(){return unCStr("CM");}),new T(function(){return unCStr("Cameroon");})),new T2(1,new T2(0,new T(function(){return unCStr("CA");}),new T(function(){return unCStr("Canada");})),new T2(1,new T2(0,new T(function(){return unCStr("CV");}),new T(function(){return unCStr("Cape Verde");})),new T2(1,new T2(0,new T(function(){return unCStr("KY");}),new T(function(){return unCStr("Cayman Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("CF");}),new T(function(){return unCStr("Central African Republic");})),new T2(1,new T2(0,new T(function(){return unCStr("TD");}),new T(function(){return unCStr("Chad");})),new T2(1,new T2(0,new T(function(){return unCStr("CL");}),new T(function(){return unCStr("Chile");})),new T2(1,new T2(0,new T(function(){return unCStr("CN");}),new T(function(){return unCStr("China");})),new T2(1,new T2(0,new T(function(){return unCStr("CX");}),new T(function(){return unCStr("Christmas Island");})),new T2(1,new T2(0,new T(function(){return unCStr("CC");}),new T(function(){return unCStr("Cocos (Keeling) Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("CO");}),new T(function(){return unCStr("Colombia");})),new T2(1,new T2(0,new T(function(){return unCStr("KM");}),new T(function(){return unCStr("Comoros");})),new T2(1,new T2(0,new T(function(){return unCStr("CG");}),new T(function(){return unCStr("Congo");})),new T2(1,new T2(0,new T(function(){return unCStr("CD");}),new T(function(){return unCStr("Congo, the Democratic Republic of the");})),new T2(1,new T2(0,new T(function(){return unCStr("CK");}),new T(function(){return unCStr("Cook Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("CR");}),new T(function(){return unCStr("Costa Rica");})),new T2(1,new T2(0,new T(function(){return unCStr("CI");}),new T(function(){return unCStr("C\u00f4te d\'Ivoire");})),new T2(1,new T2(0,new T(function(){return unCStr("HR");}),new T(function(){return unCStr("Croatia");})),new T2(1,new T2(0,new T(function(){return unCStr("CU");}),new T(function(){return unCStr("Cuba");})),new T2(1,new T2(0,new T(function(){return unCStr("CW");}),new T(function(){return unCStr("Cura\u00e7ao");})),new T2(1,new T2(0,new T(function(){return unCStr("CY");}),new T(function(){return unCStr("Cyprus");})),new T2(1,new T2(0,new T(function(){return unCStr("CZ");}),new T(function(){return unCStr("Czech Republic");})),new T2(1,new T2(0,new T(function(){return unCStr("DK");}),new T(function(){return unCStr("Denmark");})),new T2(1,new T2(0,new T(function(){return unCStr("DJ");}),new T(function(){return unCStr("Djibouti");})),new T2(1,new T2(0,new T(function(){return unCStr("DM");}),new T(function(){return unCStr("Dominica");})),new T2(1,new T2(0,new T(function(){return unCStr("DO");}),new T(function(){return unCStr("Dominican Republic");})),new T2(1,new T2(0,new T(function(){return unCStr("EC");}),new T(function(){return unCStr("Ecuador");})),new T2(1,new T2(0,new T(function(){return unCStr("EG");}),new T(function(){return unCStr("Egypt");})),new T2(1,new T2(0,new T(function(){return unCStr("SV");}),new T(function(){return unCStr("El Salvador");})),new T2(1,new T2(0,new T(function(){return unCStr("GQ");}),new T(function(){return unCStr("Equatorial Guinea");})),new T2(1,new T2(0,new T(function(){return unCStr("ER");}),new T(function(){return unCStr("Eritrea");})),new T2(1,new T2(0,new T(function(){return unCStr("EE");}),new T(function(){return unCStr("Estonia");})),new T2(1,new T2(0,new T(function(){return unCStr("ET");}),new T(function(){return unCStr("Ethiopia");})),new T2(1,new T2(0,new T(function(){return unCStr("FK");}),new T(function(){return unCStr("Falkland Islands (Malvinas)");})),new T2(1,new T2(0,new T(function(){return unCStr("FO");}),new T(function(){return unCStr("Faroe Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("FJ");}),new T(function(){return unCStr("Fiji");})),new T2(1,new T2(0,new T(function(){return unCStr("FI");}),new T(function(){return unCStr("Finland");})),new T2(1,new T2(0,new T(function(){return unCStr("FR");}),new T(function(){return unCStr("France");})),new T2(1,new T2(0,new T(function(){return unCStr("GF");}),new T(function(){return unCStr("French Guiana");})),new T2(1,new T2(0,new T(function(){return unCStr("PF");}),new T(function(){return unCStr("French Polynesia");})),new T2(1,new T2(0,new T(function(){return unCStr("TF");}),new T(function(){return unCStr("French Southern Territories");})),new T2(1,new T2(0,new T(function(){return unCStr("GA");}),new T(function(){return unCStr("Gabon");})),new T2(1,new T2(0,new T(function(){return unCStr("GM");}),new T(function(){return unCStr("Gambia");})),new T2(1,new T2(0,new T(function(){return unCStr("GE");}),new T(function(){return unCStr("Georgia");})),new T2(1,new T2(0,new T(function(){return unCStr("DE");}),new T(function(){return unCStr("Germany");})),new T2(1,new T2(0,new T(function(){return unCStr("GH");}),new T(function(){return unCStr("Ghana");})),new T2(1,new T2(0,new T(function(){return unCStr("GI");}),new T(function(){return unCStr("Gibraltar");})),new T2(1,new T2(0,new T(function(){return unCStr("GR");}),new T(function(){return unCStr("Greece");})),new T2(1,new T2(0,new T(function(){return unCStr("GL");}),new T(function(){return unCStr("Greenland");})),new T2(1,new T2(0,new T(function(){return unCStr("GD");}),new T(function(){return unCStr("Grenada");})),new T2(1,new T2(0,new T(function(){return unCStr("GP");}),new T(function(){return unCStr("Guadeloupe");})),new T2(1,new T2(0,new T(function(){return unCStr("GU");}),new T(function(){return unCStr("Guam");})),new T2(1,new T2(0,new T(function(){return unCStr("GT");}),new T(function(){return unCStr("Guatemala");})),new T2(1,new T2(0,new T(function(){return unCStr("GG");}),new T(function(){return unCStr("Guernsey");})),new T2(1,new T2(0,new T(function(){return unCStr("GN");}),new T(function(){return unCStr("Guinea");})),new T2(1,new T2(0,new T(function(){return unCStr("GW");}),new T(function(){return unCStr("Guinea-Bissau");})),new T2(1,new T2(0,new T(function(){return unCStr("GY");}),new T(function(){return unCStr("Guyana");})),new T2(1,new T2(0,new T(function(){return unCStr("HT");}),new T(function(){return unCStr("Haiti");})),new T2(1,new T2(0,new T(function(){return unCStr("HM");}),new T(function(){return unCStr("Heard Island and McDonald Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("VA");}),new T(function(){return unCStr("Holy See (Vatican City State)");})),new T2(1,new T2(0,new T(function(){return unCStr("HN");}),new T(function(){return unCStr("Honduras");})),new T2(1,new T2(0,new T(function(){return unCStr("HK");}),new T(function(){return unCStr("Hong Kong");})),new T2(1,new T2(0,new T(function(){return unCStr("HU");}),new T(function(){return unCStr("Hungary");})),new T2(1,new T2(0,new T(function(){return unCStr("IS");}),new T(function(){return unCStr("Iceland");})),new T2(1,new T2(0,new T(function(){return unCStr("IN");}),new T(function(){return unCStr("India");})),new T2(1,new T2(0,new T(function(){return unCStr("ID");}),new T(function(){return unCStr("Indonesia");})),new T2(1,new T2(0,new T(function(){return unCStr("IR");}),new T(function(){return unCStr("Iran, Islamic Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("IQ");}),new T(function(){return unCStr("Iraq");})),new T2(1,new T2(0,new T(function(){return unCStr("IE");}),new T(function(){return unCStr("Ireland");})),new T2(1,new T2(0,new T(function(){return unCStr("IM");}),new T(function(){return unCStr("Isle of Man");})),new T2(1,new T2(0,new T(function(){return unCStr("IL");}),new T(function(){return unCStr("Israel");})),new T2(1,new T2(0,new T(function(){return unCStr("IT");}),new T(function(){return unCStr("Italy");})),new T2(1,new T2(0,new T(function(){return unCStr("JM");}),new T(function(){return unCStr("Jamaica");})),new T2(1,new T2(0,new T(function(){return unCStr("JP");}),new T(function(){return unCStr("Japan");})),new T2(1,new T2(0,new T(function(){return unCStr("JE");}),new T(function(){return unCStr("Jersey");})),new T2(1,new T2(0,new T(function(){return unCStr("JO");}),new T(function(){return unCStr("Jordan");})),new T2(1,new T2(0,new T(function(){return unCStr("KZ");}),new T(function(){return unCStr("Kazakhstan");})),new T2(1,new T2(0,new T(function(){return unCStr("KE");}),new T(function(){return unCStr("Kenya");})),new T2(1,new T2(0,new T(function(){return unCStr("KI");}),new T(function(){return unCStr("Kiribati");})),new T2(1,new T2(0,new T(function(){return unCStr("KP");}),new T(function(){return unCStr("Korea, Democratic People\'s Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("KR");}),new T(function(){return unCStr("Korea, Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("KW");}),new T(function(){return unCStr("Kuwait");})),new T2(1,new T2(0,new T(function(){return unCStr("KG");}),new T(function(){return unCStr("Kyrgyzstan");})),new T2(1,new T2(0,new T(function(){return unCStr("LA");}),new T(function(){return unCStr("Lao People\'s Democratic Republic");})),new T2(1,new T2(0,new T(function(){return unCStr("LV");}),new T(function(){return unCStr("Latvia");})),new T2(1,new T2(0,new T(function(){return unCStr("LB");}),new T(function(){return unCStr("Lebanon");})),new T2(1,new T2(0,new T(function(){return unCStr("LS");}),new T(function(){return unCStr("Lesotho");})),new T2(1,new T2(0,new T(function(){return unCStr("LR");}),new T(function(){return unCStr("Liberia");})),new T2(1,new T2(0,new T(function(){return unCStr("LY");}),new T(function(){return unCStr("Libya");})),new T2(1,new T2(0,new T(function(){return unCStr("LI");}),new T(function(){return unCStr("Liechtenstein");})),new T2(1,new T2(0,new T(function(){return unCStr("LT");}),new T(function(){return unCStr("Lithuania");})),new T2(1,new T2(0,new T(function(){return unCStr("LU");}),new T(function(){return unCStr("Luxembourg");})),new T2(1,new T2(0,new T(function(){return unCStr("MO");}),new T(function(){return unCStr("Macao");})),new T2(1,new T2(0,new T(function(){return unCStr("MK");}),new T(function(){return unCStr("Macedonia, the former Yugoslav Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("MG");}),new T(function(){return unCStr("Madagascar");})),new T2(1,new T2(0,new T(function(){return unCStr("MW");}),new T(function(){return unCStr("Malawi");})),new T2(1,new T2(0,new T(function(){return unCStr("MY");}),new T(function(){return unCStr("Malaysia");})),new T2(1,new T2(0,new T(function(){return unCStr("MV");}),new T(function(){return unCStr("Maldives");})),new T2(1,new T2(0,new T(function(){return unCStr("ML");}),new T(function(){return unCStr("Mali");})),new T2(1,new T2(0,new T(function(){return unCStr("MT");}),new T(function(){return unCStr("Malta");})),new T2(1,new T2(0,new T(function(){return unCStr("MH");}),new T(function(){return unCStr("Marshall Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("MQ");}),new T(function(){return unCStr("Martinique");})),new T2(1,new T2(0,new T(function(){return unCStr("MR");}),new T(function(){return unCStr("Mauritania");})),new T2(1,new T2(0,new T(function(){return unCStr("MU");}),new T(function(){return unCStr("Mauritius");})),new T2(1,new T2(0,new T(function(){return unCStr("YT");}),new T(function(){return unCStr("Mayotte");})),new T2(1,new T2(0,new T(function(){return unCStr("MX");}),new T(function(){return unCStr("Mexico");})),new T2(1,new T2(0,new T(function(){return unCStr("FM");}),new T(function(){return unCStr("Micronesia, Federated States of");})),new T2(1,new T2(0,new T(function(){return unCStr("MD");}),new T(function(){return unCStr("Moldova, Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("MC");}),new T(function(){return unCStr("Monaco");})),new T2(1,new T2(0,new T(function(){return unCStr("MN");}),new T(function(){return unCStr("Mongolia");})),new T2(1,new T2(0,new T(function(){return unCStr("ME");}),new T(function(){return unCStr("Montenegro");})),new T2(1,new T2(0,new T(function(){return unCStr("MS");}),new T(function(){return unCStr("Montserrat");})),new T2(1,new T2(0,new T(function(){return unCStr("MA");}),new T(function(){return unCStr("Morocco");})),new T2(1,new T2(0,new T(function(){return unCStr("MZ");}),new T(function(){return unCStr("Mozambique");})),new T2(1,new T2(0,new T(function(){return unCStr("MM");}),new T(function(){return unCStr("Myanmar");})),new T2(1,new T2(0,new T(function(){return unCStr("NA");}),new T(function(){return unCStr("Namibia");})),new T2(1,new T2(0,new T(function(){return unCStr("NR");}),new T(function(){return unCStr("Nauru");})),new T2(1,new T2(0,new T(function(){return unCStr("NP");}),new T(function(){return unCStr("Nepal");})),new T2(1,new T2(0,new T(function(){return unCStr("NL");}),new T(function(){return unCStr("Netherlands");})),new T2(1,new T2(0,new T(function(){return unCStr("NC");}),new T(function(){return unCStr("New Caledonia");})),new T2(1,new T2(0,new T(function(){return unCStr("NZ");}),new T(function(){return unCStr("New Zealand");})),new T2(1,new T2(0,new T(function(){return unCStr("NI");}),new T(function(){return unCStr("Nicaragua");})),new T2(1,new T2(0,new T(function(){return unCStr("NE");}),new T(function(){return unCStr("Niger");})),new T2(1,new T2(0,new T(function(){return unCStr("NG");}),new T(function(){return unCStr("Nigeria");})),new T2(1,new T2(0,new T(function(){return unCStr("NU");}),new T(function(){return unCStr("Niue");})),new T2(1,new T2(0,new T(function(){return unCStr("NF");}),new T(function(){return unCStr("Norfolk Island");})),new T2(1,new T2(0,new T(function(){return unCStr("MP");}),new T(function(){return unCStr("Northern Mariana Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("NO");}),new T(function(){return unCStr("Norway");})),new T2(1,new T2(0,new T(function(){return unCStr("OM");}),new T(function(){return unCStr("Oman");})),new T2(1,new T2(0,new T(function(){return unCStr("PK");}),new T(function(){return unCStr("Pakistan");})),new T2(1,new T2(0,new T(function(){return unCStr("PW");}),new T(function(){return unCStr("Palau");})),new T2(1,new T2(0,new T(function(){return unCStr("PS");}),new T(function(){return unCStr("Palestinian Territory, Occupied");})),new T2(1,new T2(0,new T(function(){return unCStr("PA");}),new T(function(){return unCStr("Panama");})),new T2(1,new T2(0,new T(function(){return unCStr("PG");}),new T(function(){return unCStr("Papua New Guinea");})),new T2(1,new T2(0,new T(function(){return unCStr("PY");}),new T(function(){return unCStr("Paraguay");})),new T2(1,new T2(0,new T(function(){return unCStr("PE");}),new T(function(){return unCStr("Peru");})),new T2(1,new T2(0,new T(function(){return unCStr("PH");}),new T(function(){return unCStr("Philippines");})),new T2(1,new T2(0,new T(function(){return unCStr("PN");}),new T(function(){return unCStr("Pitcairn");})),new T2(1,new T2(0,new T(function(){return unCStr("PL");}),new T(function(){return unCStr("Poland");})),new T2(1,new T2(0,new T(function(){return unCStr("PT");}),new T(function(){return unCStr("Portugal");})),new T2(1,new T2(0,new T(function(){return unCStr("PR");}),new T(function(){return unCStr("Puerto Rico");})),new T2(1,new T2(0,new T(function(){return unCStr("QA");}),new T(function(){return unCStr("Qatar");})),new T2(1,new T2(0,new T(function(){return unCStr("RE");}),new T(function(){return unCStr("R\u00e9union");})),new T2(1,new T2(0,new T(function(){return unCStr("RO");}),new T(function(){return unCStr("Romania");})),new T2(1,new T2(0,new T(function(){return unCStr("RU");}),new T(function(){return unCStr("Russian Federation");})),new T2(1,new T2(0,new T(function(){return unCStr("RW");}),new T(function(){return unCStr("Rwanda");})),new T2(1,new T2(0,new T(function(){return unCStr("BL");}),new T(function(){return unCStr("Saint Barth\u00e9lemy");})),new T2(1,new T2(0,new T(function(){return unCStr("SH");}),new T(function(){return unCStr("Saint Helena, Ascension and Tristan da Cunha");})),new T2(1,new T2(0,new T(function(){return unCStr("KN");}),new T(function(){return unCStr("Saint Kitts and Nevis");})),new T2(1,new T2(0,new T(function(){return unCStr("LC");}),new T(function(){return unCStr("Saint Lucia");})),new T2(1,new T2(0,new T(function(){return unCStr("MF");}),new T(function(){return unCStr("Saint Martin (French part)");})),new T2(1,new T2(0,new T(function(){return unCStr("PM");}),new T(function(){return unCStr("Saint Pierre and Miquelon");})),new T2(1,new T2(0,new T(function(){return unCStr("VC");}),new T(function(){return unCStr("Saint Vincent and the Grenadines");})),new T2(1,new T2(0,new T(function(){return unCStr("WS");}),new T(function(){return unCStr("Samoa");})),new T2(1,new T2(0,new T(function(){return unCStr("SM");}),new T(function(){return unCStr("San Marino");})),new T2(1,new T2(0,new T(function(){return unCStr("ST");}),new T(function(){return unCStr("Sao Tome and Principe");})),new T2(1,new T2(0,new T(function(){return unCStr("SA");}),new T(function(){return unCStr("Saudi Arabia");})),new T2(1,new T2(0,new T(function(){return unCStr("SN");}),new T(function(){return unCStr("Senegal");})),new T2(1,new T2(0,new T(function(){return unCStr("RS");}),new T(function(){return unCStr("Serbia");})),new T2(1,new T2(0,new T(function(){return unCStr("SC");}),new T(function(){return unCStr("Seychelles");})),new T2(1,new T2(0,new T(function(){return unCStr("SL");}),new T(function(){return unCStr("Sierra Leone");})),new T2(1,new T2(0,new T(function(){return unCStr("SG");}),new T(function(){return unCStr("Singapore");})),new T2(1,new T2(0,new T(function(){return unCStr("SX");}),new T(function(){return unCStr("Sint Maarten (Dutch part)");})),new T2(1,new T2(0,new T(function(){return unCStr("SK");}),new T(function(){return unCStr("Slovakia");})),new T2(1,new T2(0,new T(function(){return unCStr("SI");}),new T(function(){return unCStr("Slovenia");})),new T2(1,new T2(0,new T(function(){return unCStr("SB");}),new T(function(){return unCStr("Solomon Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("SO");}),new T(function(){return unCStr("Somalia");})),new T2(1,new T2(0,new T(function(){return unCStr("ZA");}),new T(function(){return unCStr("South Africa");})),new T2(1,new T2(0,new T(function(){return unCStr("GS");}),new T(function(){return unCStr("South Georgia and the South Sandwich Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("SS");}),new T(function(){return unCStr("South Sudan");})),new T2(1,new T2(0,new T(function(){return unCStr("ES");}),new T(function(){return unCStr("Spain");})),new T2(1,new T2(0,new T(function(){return unCStr("LK");}),new T(function(){return unCStr("Sri Lanka");})),new T2(1,new T2(0,new T(function(){return unCStr("SD");}),new T(function(){return unCStr("Sudan");})),new T2(1,new T2(0,new T(function(){return unCStr("SR");}),new T(function(){return unCStr("Suriname");})),new T2(1,new T2(0,new T(function(){return unCStr("SJ");}),new T(function(){return unCStr("Svalbard and Jan Mayen");})),new T2(1,new T2(0,new T(function(){return unCStr("SZ");}),new T(function(){return unCStr("Swaziland");})),new T2(1,new T2(0,new T(function(){return unCStr("SE");}),new T(function(){return unCStr("Sweden");})),new T2(1,new T2(0,new T(function(){return unCStr("CH");}),new T(function(){return unCStr("Switzerland");})),new T2(1,new T2(0,new T(function(){return unCStr("SY");}),new T(function(){return unCStr("Syrian Arab Republic");})),new T2(1,new T2(0,new T(function(){return unCStr("TW");}),new T(function(){return unCStr("Taiwan, Province of China");})),new T2(1,new T2(0,new T(function(){return unCStr("TJ");}),new T(function(){return unCStr("Tajikistan");})),new T2(1,new T2(0,new T(function(){return unCStr("TZ");}),new T(function(){return unCStr("Tanzania, United Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("TH");}),new T(function(){return unCStr("Thailand");})),new T2(1,new T2(0,new T(function(){return unCStr("TL");}),new T(function(){return unCStr("Timor-Leste");})),new T2(1,new T2(0,new T(function(){return unCStr("TG");}),new T(function(){return unCStr("Togo");})),new T2(1,new T2(0,new T(function(){return unCStr("TK");}),new T(function(){return unCStr("Tokelau");})),new T2(1,new T2(0,new T(function(){return unCStr("TO");}),new T(function(){return unCStr("Tonga");})),new T2(1,new T2(0,new T(function(){return unCStr("TT");}),new T(function(){return unCStr("Trinidad and Tobago");})),new T2(1,new T2(0,new T(function(){return unCStr("TN");}),new T(function(){return unCStr("Tunisia");})),new T2(1,new T2(0,new T(function(){return unCStr("TR");}),new T(function(){return unCStr("Turkey");})),new T2(1,new T2(0,new T(function(){return unCStr("TM");}),new T(function(){return unCStr("Turkmenistan");})),new T2(1,new T2(0,new T(function(){return unCStr("TC");}),new T(function(){return unCStr("Turks and Caicos Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("TV");}),new T(function(){return unCStr("Tuvalu");})),new T2(1,new T2(0,new T(function(){return unCStr("UG");}),new T(function(){return unCStr("Uganda");})),new T2(1,new T2(0,new T(function(){return unCStr("UA");}),new T(function(){return unCStr("Ukraine");})),new T2(1,new T2(0,new T(function(){return unCStr("AE");}),new T(function(){return unCStr("United Arab Emirates");})),new T2(1,new T2(0,new T(function(){return unCStr("GB");}),new T(function(){return unCStr("United Kingdom");})),new T2(1,new T2(0,new T(function(){return unCStr("US");}),new T(function(){return unCStr("United States");})),new T2(1,new T2(0,new T(function(){return unCStr("UM");}),new T(function(){return unCStr("United States Minor Outlying Islands");})),new T2(1,new T2(0,new T(function(){return unCStr("UY");}),new T(function(){return unCStr("Uruguay");})),new T2(1,new T2(0,new T(function(){return unCStr("UZ");}),new T(function(){return unCStr("Uzbekistan");})),new T2(1,new T2(0,new T(function(){return unCStr("VU");}),new T(function(){return unCStr("Vanuatu");})),new T2(1,new T2(0,new T(function(){return unCStr("VE");}),new T(function(){return unCStr("Venezuela, Bolivarian Republic of");})),new T2(1,new T2(0,new T(function(){return unCStr("VN");}),new T(function(){return unCStr("Viet Nam");})),new T2(1,new T2(0,new T(function(){return unCStr("VG");}),new T(function(){return unCStr("Virgin Islands, British");})),new T2(1,new T2(0,new T(function(){return unCStr("VI");}),new T(function(){return unCStr("Virgin Islands, U.S.");})),new T2(1,new T2(0,new T(function(){return unCStr("WF");}),new T(function(){return unCStr("Wallis and Futuna");})),new T2(1,new T2(0,new T(function(){return unCStr("EH");}),new T(function(){return unCStr("Western Sahara");})),new T2(1,new T2(0,new T(function(){return unCStr("YE");}),new T(function(){return unCStr("Yemen");})),new T2(1,new T2(0,new T(function(){return unCStr("ZM");}),new T(function(){return unCStr("Zambia");})),new T2(1,new T2(0,new T(function(){return unCStr("ZW");}),new T(function(){return unCStr("Zimbabwe");})),__Z))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))),new T2(1,new T1(0,{_:0,a:new T1(1,new T(function(){return unCStr("Institution name");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z}),new T2(1,new T1(0,{_:0,a:new T1(1,new T(function(){return unCStr("Organisation unit");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z}),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Level of unit");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T1(0,new T(function(){return unCStr("institution");})),new T2(1,new T1(0,new T(function(){return unCStr("faculty");})),new T2(1,new T1(0,new T(function(){return unCStr("department");})),new T2(1,new T1(0,new T(function(){return unCStr("research group");})),__Z))))),__Z))))),new T2(1,_7d,__Z)))),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("1.Production ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you produce raw data?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T3(1,__Z,new T(function(){return unCStr("Yes");}),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Type of data");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("(Estimated) volume of raw data produced inhouse in 2015");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T3(8,{_:0,a:new T1(1,new T(function(){return unCStr("Genomics");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T2(3,{_:0,a:_7t,b:__Z,c:new T1(1,_7v),d:_7r,e:__Z,f:__Z,g:__Z,h:true,i:_7w},_7q),new T2(1,new T2(3,{_:0,a:_7p,b:__Z,c:new T1(1,_7m),d:__Z,e:_7o,f:__Z,g:__Z,h:false,i:_7n},_7e),__Z))),new T2(1,new T3(8,{_:0,a:new T1(1,new T(function(){return unCStr("Proteomics");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T2(3,{_:0,a:_7t,b:__Z,c:new T1(1,_7u),d:_7r,e:__Z,f:__Z,g:__Z,h:true,i:_7w},_7q),new T2(1,new T2(3,{_:0,a:_7p,b:__Z,c:new T1(1,_7l),d:__Z,e:_7o,f:__Z,g:__Z,h:false,i:_7n},_7e),__Z))),new T2(1,new T3(8,{_:0,a:new T1(1,new T(function(){return unCStr("Others");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T1(0,{_:0,a:new T1(1,new T(function(){return unCStr("Specify the output type of raw data");})),b:__Z,c:__Z,d:__Z,e:__Z,f:new T1(1,new T(function(){return unCStr("Images, chips, spectra, ...");})),g:__Z,h:true,i:__Z}),new T2(1,new T2(3,{_:0,a:_7t,b:__Z,c:new T1(1,_7s),d:_7r,e:__Z,f:__Z,g:__Z,h:true,i:_7w},_7q),new T2(1,new T2(3,{_:0,a:_7p,b:__Z,c:new T1(1,_7k),d:__Z,e:_7o,f:__Z,g:__Z,h:false,i:_7n},_7e),__Z)))),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Raw data production volume");})),b:__Z,c:new T1(1,_7j),d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:new T2(1,_7f,new T2(1,_7i,__Z))},new T1(0,_7h)),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Raw data production cost");})),b:__Z,c:new T1(1,_7g),d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:new T2(1,_7f,__Z)},_7e),__Z)))))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Funding");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Skip if you do not want to share");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Institutional");})),b:__Z,c:new T1(1,_7K),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7P},_7x),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("National");})),b:__Z,c:new T1(1,_7O),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7P},_7x),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("European");})),b:__Z,c:new T1(1,_7N),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7P},_7x),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("World-wide");})),b:__Z,c:new T1(1,_7M),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7P},_7x),new T2(1,new T2(3,{_:0,a:_7B,b:__Z,c:new T1(1,_7L),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7y},_7x),__Z)))))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Accesibility modes of your data:");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Internal inside project / collaboration");})),b:__Z,c:new T1(1,_7H),d:new T2(1,new T(function(){return unCStr("box_5_i");}),__Z),e:__Z,f:__Z,g:__Z,h:true,i:_7I},_7x),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External closed access");})),b:__Z,c:new T1(1,_7G),d:new T2(1,_7J,new T2(1,new T(function(){return unCStr("arrow_5_ca");}),__Z)),e:new T1(1,new T(function(){return unCStr("E.g. based on contract");})),f:__Z,g:__Z,h:true,i:_7I},_7x),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External open access");})),b:__Z,c:new T1(1,_7F),d:new T2(1,_7J,new T2(1,new T(function(){return unCStr("arrow_5_oa");}),__Z)),e:new T1(1,new T(function(){return unCStr("Free or paid");})),f:__Z,g:__Z,h:true,i:_7I},_7x),new T2(1,new T2(3,{_:0,a:_7B,b:__Z,c:new T1(1,_7A),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7y},_7x),__Z))))),new T2(1,_7d,__Z))))),new T2(1,new T1(0,new T(function(){return unCStr("No");})),__Z))),__Z)),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("2.Processing ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you process raw data, i.e. you produce secondary data?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T3(1,__Z,_8o,new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Input data (for 2015)");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Inhouse produced data volume");})),b:__Z,c:new T1(1,new T(function(){return unCStr("prim-raw-volume");})),d:new T2(1,new T(function(){return unCStr("arrow_1_2");}),__Z),e:__Z,f:__Z,g:__Z,h:false,i:new T2(1,_7f,__Z)},new T1(0,_8a)),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Incoming external specific raw data volume");})),b:__Z,c:__Z,d:new T2(1,new T(function(){return unCStr("arrow_L_2");}),__Z),e:new T1(1,new T(function(){return unCStr("External data that are not publicly available and are produced specifically for your needs.");})),f:__Z,g:__Z,h:true,i:__Z},_8b),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Cost of external data purchases");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,_7R,new T2(1,new T3(7,_7S,0,new T2(1,new T2(3,{_:0,a:_89,b:__Z,c:new T1(1,_85),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_86},_7T),new T2(1,new T2(3,{_:0,a:_88,b:__Z,c:new T1(1,_84),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_86},_7T),new T2(1,new T2(3,{_:0,a:_87,b:__Z,c:new T1(1,_83),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_86},_7T),new T2(1,new T2(3,{_:0,a:_7Y,b:__Z,c:new T1(1,_82),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_86},_7T),new T2(1,new T2(3,{_:0,a:_7X,b:__Z,c:new T1(1,_7U),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7V},_7T),__Z)))))),__Z))),__Z)))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Output data volumes (for 2015)");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Resulting data volume");})),b:__Z,c:new T1(1,_8p),d:new T2(1,new T(function(){return unCStr("arrow_2_3");}),new T2(1,new T(function(){return unCStr("arrow_2_4");}),__Z)),e:new T1(1,new T(function(){return unCStr("Resulting data from this stage");})),f:__Z,g:__Z,h:true,i:new T2(1,new T2(2,_8p,new T(function(){return unCStr("sec-input-volume");})),new T2(1,_7i,__Z))},_8b),__Z)),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Cost of data processing");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Rough estimation of FTEs + investments + consumables");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,_7R,new T2(1,new T3(7,_7S,0,new T2(1,new T2(3,{_:0,a:_89,b:__Z,c:new T1(1,_8g),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8h},_7T),new T2(1,new T2(3,{_:0,a:_88,b:__Z,c:new T1(1,_8f),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8h},_7T),new T2(1,new T2(3,{_:0,a:_87,b:__Z,c:new T1(1,_8e),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8h},_7T),new T2(1,new T2(3,{_:0,a:_7Y,b:__Z,c:new T1(1,_8d),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8h},_7T),new T2(1,new T2(3,{_:0,a:_7X,b:__Z,c:new T1(1,_8c),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7V},_7T),__Z)))))),__Z))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Maintenance and data sustainability");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Data represent a valuable asset that should be persisted as long as possible. How is your situation?");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Is the data sustainability plan defined?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T1(0,_8o),_7Q)),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("How long are the data stored?");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Longest considered period");})),f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T1(0,new T(function(){return unCStr("weeks");})),new T2(1,new T1(0,new T(function(){return unCStr("months");})),new T2(1,new T1(0,new T(function(){return unCStr("years");})),new T2(1,new T1(0,new T(function(){return unCStr("not limited");})),__Z))))),__Z))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Accesibility modes of your data:");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Internal inside project / collaboration");})),b:__Z,c:new T1(1,_8l),d:new T2(1,new T(function(){return unCStr("box_5_i");}),__Z),e:__Z,f:__Z,g:__Z,h:true,i:_8m},_7T),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External closed access");})),b:__Z,c:new T1(1,_8k),d:new T2(1,_8n,new T2(1,new T(function(){return unCStr("arrow_5_ca");}),__Z)),e:new T1(1,new T(function(){return unCStr("E.g. based on contract");})),f:__Z,g:__Z,h:true,i:_8m},_7T),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External open access");})),b:__Z,c:new T1(1,_8j),d:new T2(1,_8n,new T2(1,new T(function(){return unCStr("arrow_5_oa");}),__Z)),e:new T1(1,new T(function(){return unCStr("Free or paid");})),f:__Z,g:__Z,h:true,i:_8m},_7T),new T2(1,new T2(3,{_:0,a:_7X,b:__Z,c:new T1(1,_8i),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_7V},_7T),__Z))))),new T2(1,_7d,__Z))))))),_7Q)),__Z)),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("3.Usage ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you use data, i.e. to perform analyses?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T3(1,__Z,_8R,new T2(1,new T3(7,{_:0,a:__Z,b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T1(1,{_:0,a:new T1(1,new T(function(){return unCStr("Describe the usage");})),b:__Z,c:__Z,d:__Z,e:__Z,f:new T1(1,new T(function(){return unCStr("A typical usage is performing a certain analysis.");})),g:__Z,h:false,i:__Z}),__Z)),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Input data (for 2015)");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Inhouse produced data volume");})),b:__Z,c:new T1(1,new T(function(){return unCStr("sec-input-volume");})),d:new T2(1,new T(function(){return unCStr("arrow_2_3");}),__Z),e:__Z,f:__Z,g:__Z,h:false,i:new T2(1,_7f,__Z)},new T1(0,_8S)),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Incoming external specific raw data volume");})),b:__Z,c:__Z,d:new T2(1,new T(function(){return unCStr("arrow_L_3");}),__Z),e:new T1(1,new T(function(){return unCStr("External data that are not publicly available and are produced specifically for your needs.");})),f:__Z,g:__Z,h:true,i:__Z},_8T),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Cost of external data purchases");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,_8J,new T2(1,new T3(7,_8I,0,new T2(1,new T2(3,{_:0,a:_8H,b:__Z,c:new T1(1,_8Y),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8Z},_8v),new T2(1,new T2(3,{_:0,a:_8G,b:__Z,c:new T1(1,_8X),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8Z},_8v),new T2(1,new T2(3,{_:0,a:_8F,b:__Z,c:new T1(1,_8W),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8Z},_8v),new T2(1,new T2(3,{_:0,a:_8E,b:__Z,c:new T1(1,_8V),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8Z},_8v),new T2(1,new T2(3,{_:0,a:_8u,b:__Z,c:new T1(1,_8U),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8s},_8v),__Z)))))),__Z))),__Z)))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Output data volumes (for 2015)");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Resulting data volume");})),b:__Z,c:new T1(1,new T(function(){return unCStr("sec-volume");})),d:new T2(1,new T(function(){return unCStr("arrow_3_4");}),__Z),e:new T1(1,new T(function(){return unCStr("Resulting data from this stage");})),f:__Z,g:__Z,h:true,i:new T2(1,_7i,__Z)},_8T),__Z)),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Cost of secondary data production");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Rough estimation of FTEs + investments + consumables");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,_8J,new T2(1,new T3(7,_8I,0,new T2(1,new T2(3,{_:0,a:_8H,b:__Z,c:new T1(1,_8C),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8D},_8v),new T2(1,new T2(3,{_:0,a:_8G,b:__Z,c:new T1(1,_8B),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8D},_8v),new T2(1,new T2(3,{_:0,a:_8F,b:__Z,c:new T1(1,_8A),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8D},_8v),new T2(1,new T2(3,{_:0,a:_8E,b:__Z,c:new T1(1,_8z),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8D},_8v),new T2(1,new T2(3,{_:0,a:_8u,b:__Z,c:new T1(1,_8r),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8s},_8v),__Z)))))),__Z))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Maintenance and data sustainability");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Data represent a valuable asset that should be persisted as long as possible. How is your situation?");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Is the data sustainability plan defined?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T1(0,_8R),_8q)),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("How long are the data stored?");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Longest considered period");})),f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T1(0,new T(function(){return unCStr("weeks");})),new T2(1,new T1(0,new T(function(){return unCStr("months");})),new T2(1,new T1(0,new T(function(){return unCStr("years");})),new T2(1,new T1(0,new T(function(){return unCStr("not limited");})),__Z))))),__Z))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Accesibility modes of your data:");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Internal inside project / collaboration");})),b:__Z,c:new T1(1,_8N),d:new T2(1,new T(function(){return unCStr("box_5_i");}),__Z),e:__Z,f:__Z,g:__Z,h:true,i:_8O},_8v),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External closed access");})),b:__Z,c:new T1(1,_8M),d:new T2(1,_8Q,new T2(1,new T(function(){return unCStr("arrow_5_ca");}),__Z)),e:new T1(1,new T(function(){return unCStr("E.g. based on contract");})),f:__Z,g:__Z,h:true,i:_8O},_8v),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External open access");})),b:__Z,c:new T1(1,_8L),d:new T2(1,_8Q,new T2(1,new T(function(){return unCStr("arrow_5_oa");}),__Z)),e:new T1(1,new T(function(){return unCStr("Free or paid");})),f:__Z,g:__Z,h:true,i:_8O},_8v),new T2(1,new T2(3,{_:0,a:_8u,b:__Z,c:new T1(1,_8K),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_8s},_8v),__Z))))),new T2(1,_7d,__Z)))))))),_8q)),__Z)),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("4.Storage ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Data volumes");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Just scientic data volumes (without backups and scratch/tmp) are in question.");})),f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Total volume produced in 2015");})),b:__Z,c:new T1(1,new T(function(){return unCStr("total-volume");})),d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:new T2(1,_7f,__Z)},new T1(0,_98)),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Total volume of data stored at the end of 2015");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},_99),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Total volume of backups");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},_99),__Z)))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Storage providers");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Group\'s local");})),b:__Z,c:new T1(1,_94),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_95},_90),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Institutional");})),b:__Z,c:new T1(1,_93),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_95},_90),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("External Provider");})),b:__Z,c:new T1(1,_92),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:_95},_90),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Sum");})),b:__Z,c:new T1(1,_91),d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:new T2(1,_7f,new T2(1,new T1(4,function(_9o){return (E(_9o)==100)?true:false;}),__Z))},_90),__Z))))),new T2(1,_7d,__Z)))),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("5.Accessibility ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you provide data accessibility for external parties?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T3(1,__Z,new T(function(){return unCStr("Yes");}),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Accessibility details");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},1,new T2(1,new T1(1,{_:0,a:new T1(1,new T(function(){return unCStr("How do you make your data accessible?");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("For inspiration, click the red box in the figure");})),f:__Z,g:__Z,h:true,i:__Z}),new T2(1,new T1(1,{_:0,a:new T1(1,new T(function(){return unCStr("Links to your services");})),b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("URLs to web pages / data source or other accessibility link");})),f:__Z,g:__Z,h:true,i:__Z}),__Z))),__Z)),new T2(1,new T1(0,new T(function(){return unCStr("No");})),__Z))),new T2(1,_7d,__Z))),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("6.Management ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("We perform data management for:");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T3(8,{_:0,a:new T1(1,new T(function(){return unCStr("local use");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,__Z),new T2(1,new T3(8,{_:0,a:new T1(1,new T(function(){return unCStr("community use");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,__Z),__Z))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Management details");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you handle error reports?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},_9b),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you manage versioning?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},_9b),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Is data actuality maintained (updates)?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},_9b),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Sustainability");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T1(0,new T(function(){return unCStr("long-term, continuous funding");})),new T2(1,new T3(1,__Z,new T(function(){return unCStr("short-term");}),new T2(1,new T3(7,{_:0,a:__Z,b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("How long");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},_9a),__Z)),__Z)),__Z))),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Longest required sustainability");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},_9a),new T2(1,new T2(4,{_:0,a:new T1(1,new T(function(){return unCStr("Do you apply some form of data stewardship?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},new T2(1,new T3(1,__Z,new T(function(){return unCStr("Yes");}),new T2(1,new T1(1,{_:0,a:new T1(1,new T(function(){return unCStr("How?");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z}),__Z)),new T2(1,new T1(0,new T(function(){return unCStr("No");})),__Z))),__Z))))))),new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Total cost of data management");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("For year 2015");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T1(0,new T(function(){return unCStr("thousand EUR");}))),__Z)),new T2(1,_7d,__Z))))),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("7.Roles ");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T3(7,{_:0,a:new T1(1,new T(function(){return unCStr("Employed roles");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:true,i:__Z},0,new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data producer");})),b:__Z,c:__Z,d:new T2(1,_9l,__Z),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data expert");})),b:__Z,c:__Z,d:new T2(1,_9e,new T2(1,_9f,new T2(1,_9g,__Z))),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data consumer");})),b:__Z,c:__Z,d:new T2(1,_9f,__Z),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data curator");})),b:__Z,c:__Z,d:_9k,e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data custodian");})),b:__Z,c:__Z,d:new T2(1,_9g,new T2(1,_9i,new T2(1,_9h,__Z))),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data steward");})),b:__Z,c:__Z,d:new T2(1,_9l,_9k),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),new T2(1,new T2(3,{_:0,a:new T1(1,new T(function(){return unCStr("Data manager");})),b:__Z,c:__Z,d:new T2(1,_9l,new T2(1,_9e,_9j)),e:__Z,f:__Z,g:_9d,h:false,i:__Z},_9c),__Z)))))))),new T2(1,_7d,__Z))),new T2(1,new T2(6,{_:0,a:new T1(1,new T(function(){return unCStr("Finish");})),b:__Z,c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},new T2(1,new T1(10,{_:0,a:__Z,b:__Z,c:__Z,d:__Z,e:new T1(1,new T(function(){return unCStr("Save your answers.");})),f:__Z,g:__Z,h:true,i:__Z}),__Z)),__Z))))))))),new T2(1,_9m,0),__Z).b);}),_9p=function(_9q,_9r){while(1){var _9s=(function(_9t,_9u){var _9v=E(_9t);if(!_9v._){return E(_9u);}else{var _9w=_R(_9u,new T(function(){var _9x=E(_9v.a);if(!_9x._){return __Z;}else{return E(_9x.c);}},1));_9q=_9v.b;_9r=_9w;return __continue;}})(_9q,_9r);if(_9s!=__continue){return _9s;}}},_9y=function(_9z){var _9A=E(_9z);switch(_9A._){case 0:return E(_9A.b);case 5:return _9p(_9A.b,__Z);case 7:return E(_9A.b);case 8:return E(_9A.c);case 9:return E(_9A.b);default:return __Z;}},_9B=function(_9C,_9D,_){var _9E=(function (cls, jq) { jq.addClass(cls); return jq; });return _9E(toJSStr(E(_9C)),_9D);},_9F=function(_9G,_9H,_9I,_){var _9J=(function (k, v, jq) { jq.attr(k, v); return jq; });return _9J(toJSStr(E(_9G)),toJSStr(E(_9H)),_9I);},_9K=new T(function(){return (function (jq) { return jq.parent(); });}),_9L=new T(function(){return (function (jq) { return jq.last(); });}),_9M=new T(function(){return (function (jq) { return jq.children(); });}),_9N=function(_9O,_9P,_9Q,_){var _9R=E(_9M)(_9Q),_9S=E(_9L)(_9R),_9T=_9F(_9O,_9P,_9S,_);return C > 19 ? new F(function(){return E(_9K)(E(_9T));}) : (++C,E(_9K)(E(_9T)));},_9U=function(_9V,_9W,_9X,_){var _9Y=E(_9M)(_9X),_9Z=E(_9L)(_9Y),_a0=_3h(_9V,_9W,_9Z,_);return C > 19 ? new F(function(){return E(_9K)(E(_a0));}) : (++C,E(_9K)(E(_a0)));},_a1=function(_a2,_a3,_){var _a4=(function (tag, jq) { return jq.append(tag); });return _a4(toJSStr(E(_a2)),_a3);},_a5=function(_a6,_a7,_){var _a8=E(_9M)(_a7),_a9=E(_9L)(_a8),_aa=(function (txt, jq) { jq.text(txt); return jq; }),_ab=_aa(toJSStr(E(_a6)),_a9);return C > 19 ? new F(function(){return E(_9K)(_ab);}) : (++C,E(_9K)(_ab));},_ac=new T(function(){return (function (jq, toJq) { return toJq.append(jq); });}),_ad=new T(function(){return unCStr("<ul>");}),_ae=new T(function(){return unCStr("nav");}),_af=new T(function(){return unCStr("<li>");}),_ag=new T(function(){return unCStr("id");}),_ah=new T(function(){return unCStr("<a>");}),_ai=new T(function(){return unCStr("<div class=\'stripe stripe-thin\'>");}),_aj=new T(function(){return unCStr("display");}),_ak=new T(function(){return unCStr("none");}),_al=new T(function(){return unCStr("class");}),_am=new T(function(){return unCStr("inside-bordered");}),_an=function(_ao,_ap,_){var _aq=__createJSFunc(2,function(_ar,_){var _as=B(A2(E(_ao),_ar,_));return _2D;}),_at=E(_ap),_au=(function (ev, jq) { jq.click(ev); }),_av=_au(_aq,_at);return _at;},_aw=new T(function(){return unCStr("pane_");}),_ax=function(_ay){return _R(_aw,new T(function(){return _3Y(_3C(_3F(_ay)).b);},1));},_az=new T(function(){return unCStr("tab_");}),_aA=function(_aB){return _R(_az,new T(function(){return _3Y(_3C(_3F(_aB)).b);},1));},_aC=function(_aD){var _aE=E(_3C(_3F(_aD)).a);return (_aE._==0)?__Z:E(_aE.a);},_aF=new T(function(){return unCStr("block");}),_aG=new T(function(){return unCStr("display");}),_aH=function(_aI,_aJ){while(1){var _aK=E(_aI);if(!_aK._){return (E(_aJ)._==0)?true:false;}else{var _aL=E(_aJ);if(!_aL._){return false;}else{if(E(_aK.a)!=E(_aL.a)){return false;}else{_aI=_aK.b;_aJ=_aL.b;continue;}}}}},_aM=function(_aN,_aO){return _aH(_3Y(_3C(_3F(_aN)).b),_3Y(_3C(_3F(_aO)).b));},_aP=function(_aQ,_aR,_){var _aS=(function (cls, jq) { jq.removeClass(cls); return jq; });return _aS(toJSStr(E(_aQ)),_aR);},_aT=new T(function(){return unCStr("notcurrent");}),_aU=new T(function(){return unCStr("current");}),_aV=new T(function(){return unCStr("#");}),_aW=function(_aX,_aY,_){var _aZ=function(_b0,_){while(1){var _b1=(function(_b2,_){var _b3=E(_b2);if(!_b3._){return 0;}else{var _b4=_b3.a,_b5=_b3.b;if(!_aM(_b4,_aX)){var _b6=_4b(_R(_aV,new T(function(){return _aA(_b4);},1)),_),_b7=_aP(_aU,E(_b6),_),_b8=_9B(_aT,E(_b7),_);_b0=_b5;return __continue;}else{var _b9=_4b(_R(_aV,new T(function(){return _aA(_b4);},1)),_),_ba=_aP(_aT,E(_b9),_),_bb=_9B(_aU,E(_ba),_);_b0=_b5;return __continue;}}})(_b0,_);if(_b1!=__continue){return _b1;}}};return _aZ(_aY,_);},_bc=new T(function(){return unCStr("none");}),_bd=function(_be,_){while(1){var _bf=E(_be);if(!_bf._){return 0;}else{var _bg=_3h(_aG,_bc,E(_bf.a),_);_be=_bf.b;continue;}}},_bh=function(_bi,_){var _bj=E(_bi);if(!_bj._){return __Z;}else{var _bk=_4b(_R(_aV,new T(function(){return _ax(_bj.a);},1)),_),_bl=_bh(_bj.b,_);return new T2(1,_bk,_bl);}},_bm=function(_bn,_bo,_){var _bp=_4b(_R(_aV,new T(function(){return _ax(_bn);},1)),_),_bq=_bh(_bo,_),_br=_aW(_bn,_bo,_),_bs=_bd(_bq,_),_bt=_3h(_aG,_aF,E(_bp),_);return 0;},_bu=function(_bv,_bw,_bx,_){var _by=_a1(_ad,_bx,_),_bz=E(_9M),_bA=_bz(E(_by)),_bB=E(_9L),_bC=_bB(_bA),_bD=_9B(_ae,_bC,_),_bE=function(_,_bF){var _bG=E(_9K)(E(_bF)),_bH=_a1(_ai,_bG,_),_bI=E(_bv);if(!_bI._){return _bH;}else{var _bJ=E(_bw);if(!_bJ._){return _bH;}else{var _bK=B(A1(_bJ.a,_)),_bL=E(_ac),_bM=_bL(E(_bK),E(_bH)),_bN=B(_9N(_ag,new T(function(){return _ax(_bI.a);},1),_bM,_)),_bO=B(_9U(_aj,_ak,E(_bN),_)),_bP=B(_9N(_al,_am,E(_bO),_)),_bQ=function(_bR,_bS,_bT,_){while(1){var _bU=(function(_bV,_bW,_bX,_){var _bY=E(_bV);if(!_bY._){return _bX;}else{var _bZ=E(_bW);if(!_bZ._){return _bX;}else{var _c0=B(A1(_bZ.a,_)),_c1=_bL(E(_c0),E(_bX)),_c2=B(_9N(_ag,new T(function(){return _ax(_bY.a);},1),_c1,_)),_c3=B(_9U(_aj,_ak,E(_c2),_)),_c4=B(_9N(_al,_am,E(_c3),_));_bR=_bY.b;_bS=_bZ.b;_bT=_c4;return __continue;}}})(_bR,_bS,_bT,_);if(_bU!=__continue){return _bU;}}};return _bQ(_bI.b,_bJ.b,_bP,_);}}},_c5=E(_bv);if(!_c5._){return _bE(_,_bD);}else{var _c6=_c5.a,_c7=_a1(_af,E(_bD),_),_c8=B(_9N(_ag,new T(function(){return _aA(_c6);},1),E(_c7),_)),_c9=_bz(E(_c8)),_ca=_bB(_c9),_cb=_a1(_ah,_ca,_),_cc=_an(function(_cd,_){return _bm(_c6,_c5,_);},_cb,_),_ce=B(_a5(new T(function(){return _aC(_c6);},1),E(_cc),_)),_cf=E(_9K),_cg=_cf(E(_ce)),_ch=function(_ci,_cj,_ck,_){while(1){var _cl=(function(_cm,_cn,_co,_){var _cp=E(_cm);if(!_cp._){return _cn;}else{var _cq=_cp.a,_cr=_a1(_af,_cn,_),_cs=B(_9N(_ag,new T(function(){return _aA(_cq);},1),E(_cr),_)),_ct=_bz(E(_cs)),_cu=_bB(_ct),_cv=_a1(_ah,_cu,_),_cw=_an(function(_cx,_){return _bm(_cq,_c5,_);},_cv,_),_cy=B(_a5(new T(function(){return _aC(_cq);},1),E(_cw),_)),_cz=_cf(E(_cy)),_cA=_;_ci=_cp.b;_cj=_cz;_ck=_cA;return __continue;}})(_ci,_cj,_ck,_);if(_cl!=__continue){return _cl;}}},_cB=_ch(_c5.b,_cg,_,_);return _bE(_,_cB);}},_cC=function(_cD,_){var _cE=(function (jq) { jq.mouseleave(); }),_cF=_cE(_cD);return _cD;},_cG=function(_cH,_cI,_){var _cJ=(function (html, jq) { jq.html(html); return jq; });return _cJ(toJSStr(E(_cH)),_cI);},_cK=function(_cL,_cM,_){var _cN=__createJSFunc(2,function(_cO,_){var _cP=B(A2(E(_cL),_cO,_));return _2D;}),_cQ=E(_cM),_cR=(function (ev, jq) { jq[0].addEventListener('load', ev); }),_cS=_cR(_cN,_cQ);return _cQ;},_cT=function(_cU,_cV,_){var _cW=E(_9M)(_cV),_cX=E(_9L)(_cW),_cY=_cK(_cU,_cX,_);return C > 19 ? new F(function(){return E(_9K)(E(_cY));}) : (++C,E(_9K)(E(_cY)));},_cZ=function(_d0,_){var _d1=(function (jq) { jq.click(); }),_d2=_d1(_d0);return _d0;},_d3=new T(function(){return unCStr("About");}),_d4=new T(function(){return unCStr("  <div>    <p>      This questionnaire aims to collect managerial information about the bioinformatics data space.    </p>    <p>      <strong>Only data where the respondent is the owner are subject of the questionnaires</strong>, i.e. not data produced as a service.    </p>    <p>      Its completion should take no more than 15 minutes. If you do not know exact answer, provide your best qualified guess.    </p>    <p>      For questions please contact <a href=\'mailto:robert.pergl@fit.cvut.cz\'>robert.pergl@fit.cvut.cz</a>.    </p>    <br>    <p style=\'font-size: 90%; font-style: italic;\'>      Version of this questionnaire: v2.0    </p>  </div> ");}),_d5=function(_){return _4b(_d4,_);},_d6=new T(function(){return unCStr("_desc-subpane-text");}),_d7=function(_d8){return _R(_3Y(_3C(_3F(_3z(_d8))).b),_d6);},_d9=new T(function(){return unCStr("diagram_");}),_da=function(_db){return _R(_d9,new T(function(){return _3Y(_3C(_3F(_3z(_db))).b);},1));},_dc=function(_dd,_de){var _df=E(_dd);if(!_df._){var _dg=_df.a,_dh=E(_de);if(!_dh._){return _aH(_dg,_dh.a);}else{return _aH(_dg,_dh.b);}}else{var _di=_df.b,_dj=E(_de);if(!_dj._){return _aH(_di,_dj.a);}else{return _aH(_di,_dj.b);}}},_dk=function(_dl,_dm){return _R(_dn(_dl),_dm);},_do=new T(function(){return unCStr("Just ");}),_dp=new T(function(){return unCStr("Nothing");}),_dq=new T(function(){return unCStr("SubmitButtonElem id=");}),_dr=new T(function(){return unCStr("SaveButtonElem id=");}),_ds=new T(function(){return unCStr("NumberElem id=");}),_dt=new T(function(){return unCStr("EmailElem id=");}),_du=new T(function(){return unCStr("TextElem id=");}),_dv=new T(function(){return unCStr("StringElem id=");}),_dw=new T(function(){return unCStr("ChapterElem id=");}),_dx=new T2(1,34,__Z),_dy=new T(function(){return unCStr("MultipleGroupElem id=");}),_dz=new T(function(){return unCStr(" children: ");}),_dA=new T(function(){return unCStr("OptionalGroupElem id=");}),_dB=new T(function(){return unCStr("SimpleGroupElem id=");}),_dC=new T(function(){return unCStr(" value=");}),_dD=new T(function(){return unCStr("ListElem id=");}),_dE=new T(function(){return unCStr("ChoiceElem id=");}),_dF=new T(function(){return unCStr(" unit=");}),_dG=new T(function(){return unCStr("ACK");}),_dH=new T(function(){return unCStr("BEL");}),_dI=new T(function(){return unCStr("BS");}),_dJ=new T(function(){return unCStr("SP");}),_dK=new T(function(){return unCStr("US");}),_dL=new T(function(){return unCStr("RS");}),_dM=new T(function(){return unCStr("GS");}),_dN=new T(function(){return unCStr("FS");}),_dO=new T(function(){return unCStr("ESC");}),_dP=new T(function(){return unCStr("SUB");}),_dQ=new T(function(){return unCStr("EM");}),_dR=new T(function(){return unCStr("CAN");}),_dS=new T(function(){return unCStr("ETB");}),_dT=new T(function(){return unCStr("SYN");}),_dU=new T(function(){return unCStr("NAK");}),_dV=new T(function(){return unCStr("DC4");}),_dW=new T(function(){return unCStr("DC3");}),_dX=new T(function(){return unCStr("DC2");}),_dY=new T(function(){return unCStr("DC1");}),_dZ=new T(function(){return unCStr("DLE");}),_e0=new T(function(){return unCStr("SI");}),_e1=new T(function(){return unCStr("SO");}),_e2=new T(function(){return unCStr("CR");}),_e3=new T(function(){return unCStr("FF");}),_e4=new T(function(){return unCStr("VT");}),_e5=new T(function(){return unCStr("LF");}),_e6=new T(function(){return unCStr("HT");}),_e7=new T(function(){return unCStr("ENQ");}),_e8=new T(function(){return unCStr("EOT");}),_e9=new T(function(){return unCStr("ETX");}),_ea=new T(function(){return unCStr("STX");}),_eb=new T(function(){return unCStr("SOH");}),_ec=new T(function(){return unCStr("NUL");}),_ed=new T(function(){return unCStr("\\DEL");}),_ee=new T(function(){return unCStr("\\a");}),_ef=new T(function(){return unCStr("\\\\");}),_eg=new T(function(){return unCStr("\\SO");}),_eh=new T(function(){return unCStr("\\r");}),_ei=new T(function(){return unCStr("\\f");}),_ej=new T(function(){return unCStr("\\v");}),_ek=new T(function(){return unCStr("\\n");}),_el=new T(function(){return unCStr("\\t");}),_em=new T(function(){return unCStr("\\b");}),_en=function(_eo,_ep){if(_eo<=127){var _eq=E(_eo);switch(_eq){case 92:return _R(_ef,_ep);case 127:return _R(_ed,_ep);default:if(_eq<32){switch(_eq){case 7:return _R(_ee,_ep);case 8:return _R(_em,_ep);case 9:return _R(_el,_ep);case 10:return _R(_ek,_ep);case 11:return _R(_ej,_ep);case 12:return _R(_ei,_ep);case 13:return _R(_eh,_ep);case 14:return _R(_eg,new T(function(){var _er=E(_ep);if(!_er._){return __Z;}else{if(E(_er.a)==72){return unAppCStr("\\&",_er);}else{return _er;}}},1));default:return _R(new T2(1,92,new T(function(){return _5Z(new T2(1,_ec,new T2(1,_eb,new T2(1,_ea,new T2(1,_e9,new T2(1,_e8,new T2(1,_e7,new T2(1,_dG,new T2(1,_dH,new T2(1,_dI,new T2(1,_e6,new T2(1,_e5,new T2(1,_e4,new T2(1,_e3,new T2(1,_e2,new T2(1,_e1,new T2(1,_e0,new T2(1,_dZ,new T2(1,_dY,new T2(1,_dX,new T2(1,_dW,new T2(1,_dV,new T2(1,_dU,new T2(1,_dT,new T2(1,_dS,new T2(1,_dR,new T2(1,_dQ,new T2(1,_dP,new T2(1,_dO,new T2(1,_dN,new T2(1,_dM,new T2(1,_dL,new T2(1,_dK,new T2(1,_dJ,__Z))))))))))))))))))))))))))))))))),_eq);})),_ep);}}else{return new T2(1,_eq,_ep);}}}else{var _es=new T(function(){var _et=jsShowI(_eo);return _R(fromJSStr(_et),new T(function(){var _eu=E(_ep);if(!_eu._){return __Z;}else{var _ev=E(_eu.a);if(_ev<48){return _eu;}else{if(_ev>57){return _eu;}else{return unAppCStr("\\&",_eu);}}}},1));});return new T2(1,92,_es);}},_ew=new T(function(){return unCStr("\\\"");}),_ex=function(_ey,_ez){var _eA=E(_ey);if(!_eA._){return E(_ez);}else{var _eB=_eA.b,_eC=E(_eA.a);if(_eC==34){return _R(_ew,new T(function(){return _ex(_eB,_ez);},1));}else{return _en(_eC,new T(function(){return _ex(_eB,_ez);}));}}},_dn=function(_eD){var _eE=E(_eD);switch(_eE._){case 0:var _eF=new T(function(){var _eG=new T(function(){return _R(_dz,new T(function(){return _1K(_dk,_eE.b,__Z);},1));},1);return _R(_3Y(_3C(_eE.a).b),_eG);},1);return _R(_dw,_eF);case 1:var _eH=new T(function(){return _R(_3Y(_3C(_eE.a).b),new T(function(){return _R(_dC,_eE.b);},1));},1);return _R(_dv,_eH);case 2:var _eI=new T(function(){return _R(_3Y(_3C(_eE.a).b),new T(function(){return _R(_dC,_eE.b);},1));},1);return _R(_du,_eI);case 3:var _eJ=new T(function(){return _R(_3Y(_3C(_eE.a).b),new T(function(){return _R(_dC,_eE.b);},1));},1);return _R(_dt,_eJ);case 4:var _eK=new T(function(){var _eL=new T(function(){var _eM=new T(function(){var _eN=new T(function(){var _eO=new T(function(){var _eP=E(_eE.c);if(!_eP._){return E(_dp);}else{return _R(_do,new T2(1,34,new T(function(){return _ex(_eP.a,_dx);})));}},1);return _R(_dF,_eO);}),_eQ=E(_eE.b);if(!_eQ._){return _R(_dp,_eN);}else{return _R(_do,new T(function(){return _R(_3q(11,E(_eQ.a),__Z),_eN);},1));}},1);return _R(_dC,_eM);},1);return _R(_3Y(_3C(_eE.a).b),_eL);},1);return _R(_ds,_eK);case 5:return _R(_dE,new T(function(){return _3Y(_3C(_eE.a).b);},1));case 6:var _eR=new T(function(){var _eS=new T(function(){var _eT=new T(function(){var _eU=E(_eE.b);if(!_eU._){return E(_dp);}else{return _R(_do,new T2(1,34,new T(function(){return _ex(_eU.a,_dx);})));}},1);return _R(_dC,_eT);},1);return _R(_3Y(_3C(_eE.a).b),_eS);},1);return _R(_dD,_eR);case 7:var _eV=new T(function(){var _eW=new T(function(){return _R(_dz,new T(function(){return _1K(_dk,_eE.b,__Z);},1));},1);return _R(_3Y(_3C(_eE.a).b),_eW);},1);return _R(_dB,_eV);case 8:var _eX=new T(function(){var _eY=new T(function(){return _R(_dz,new T(function(){return _1K(_dk,_eE.c,__Z);},1));},1);return _R(_3Y(_3C(_eE.a).b),_eY);},1);return _R(_dA,_eX);case 9:return _R(_dy,new T(function(){return _3Y(_3C(_eE.a).b);},1));case 10:return _R(_dr,new T(function(){return _3Y(_3C(_eE.a).b);},1));default:return _R(_dq,new T(function(){return _3Y(_3C(_eE.a).b);},1));}},_eZ=new T2(1,34,__Z),_f0=new T(function(){return unCStr("IntValueRule (Int -> Bool)");}),_f1=new T(function(){return unCStr("ReadOnlyRule");}),_f2=function(_f3,_f4){return new T2(1,34,new T(function(){return _ex(_f3,new T2(1,34,_f4));}));},_f5=function(_f6){var _f7=E(_f6);switch(_f7._){case 0:var _f8=new T(function(){var _f9=new T(function(){return unAppCStr(" -> ",new T2(1,34,new T(function(){return _ex(_f7.b,_eZ);})));},1);return _R(_1K(_f2,_f7.a,__Z),_f9);});return unAppCStr("SumRule @ ",_f8);case 1:var _fa=new T(function(){var _fb=new T(function(){return unAppCStr(" -> ",new T2(1,34,new T(function(){return _ex(_f7.b,_eZ);})));},1);return _R(_1K(_f2,_f7.a,__Z),_fb);});return unAppCStr("SumTBsRule @ ",_fa);case 2:var _fc=new T(function(){var _fd=new T(function(){return unAppCStr(" -> ",new T2(1,34,new T(function(){return _ex(_f7.b,_eZ);})));},1);return _R(new T2(1,34,new T(function(){return _ex(_f7.a,_eZ);})),_fd);});return unAppCStr("CopyValueRule @ ",_fc);case 3:return E(_f1);default:return E(_f0);}},_fe=function(_ff,_fg){var _fh=E(_fg);if(!_fh._){return __Z;}else{var _fi=_fh.a,_fj=function(_fk){var _fl=B(_fe(_ff,_9y(_fi)));if(!_fl._){return C > 19 ? new F(function(){return _fe(_ff,_fh.b);}) : (++C,_fe(_ff,_fh.b));}else{return E(_fl);}},_fm=E(_3C(_3F(_fi)).c);if(!_fm._){if(!_aH(__Z,_ff)){return C > 19 ? new F(function(){return _fj(_);}) : (++C,_fj(_));}else{return new T1(1,_fi);}}else{if(!_aH(_fm.a,_ff)){return C > 19 ? new F(function(){return _fj(_);}) : (++C,_fj(_));}else{return new T1(1,_fi);}}}},_fn=new T(function(){return unCStr("\']:checked");}),_fo=new T(function(){return unCStr("[name=\'");}),_fp=function(_fq,_){var _fr=(function (elId) { return $(elId); }),_fs=_fr(toJSStr(_R(_fo,new T(function(){return _R(_fq,_fn);},1)))),_ft=E(_3d)(_fs);return new T(function(){var _fu=String(_ft);return fromJSStr(_fu);});},_fv=new T(function(){return unCStr("undefined");}),_fw=new T(function(){return unCStr("_unit");}),_fx=function(_fy){while(1){var _fz=(function(_fA){var _fB=E(_fA);if(!_fB._){return __Z;}else{var _fC=_fB.b,_fD=E(_fB.a);if(!E(_fD.b)._){return new T2(1,_fD.a,new T(function(){return _fx(_fC);}));}else{_fy=_fC;return __continue;}}})(_fy);if(_fz!=__continue){return _fz;}}},_fE=function(_fF,_fG){while(1){var _fH=(function(_fI,_fJ){var _fK=E(_fI);switch(_fK._){case 0:var _fL=E(_fJ);if(!_fL._){return __Z;}else{_fF=B(A1(_fK.a,_fL.a));_fG=_fL.b;return __continue;}break;case 1:var _fM=B(A1(_fK.a,_fJ)),_fN=_fJ;_fF=_fM;_fG=_fN;return __continue;case 2:return __Z;case 3:return new T2(1,new T2(0,_fK.a,_fJ),new T(function(){return _fE(_fK.b,_fJ);}));default:return E(_fK.a);}})(_fF,_fG);if(_fH!=__continue){return _fH;}}},_fO=function(_fP,_){var _fQ=(function (name) { return $('[name="' + name + '"]'); });return _fQ(toJSStr(E(_fP)));},_fR=new T(function(){return unCStr("base");}),_fS=new T(function(){return unCStr("Control.Exception.Base");}),_fT=new T(function(){return unCStr("PatternMatchFail");}),_fU=function(_fV){return E(new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),new T5(0,new Long(18445595,3739165398,true),new Long(52003073,3246954884,true),_fR,_fS,_fT),__Z,__Z));},_fW=function(_fX){return E(E(_fX).a);},_fY=function(_fZ,_g0){return _R(E(_fZ).a,_g0);},_g1=new T(function(){return new T5(0,_fU,new T3(0,function(_g2,_g3,_g4){return _R(E(_g3).a,_g4);},_fW,function(_g5,_g6){return _1K(_fY,_g5,_g6);}),function(_g7){return new T2(0,_g1,_g7);},function(_g8){var _g9=E(_g8);return _G(_E(_g9.a),_fU,_g9.b);},_fW);}),_ga=new T(function(){return unCStr("Non-exhaustive patterns in");}),_gb=function(_gc,_gd){return die(new T(function(){return B(A2(_26,_gd,_gc));}));},_ge=function(_gf,_gg){return _gb(_gf,_gg);},_gh=function(_gi,_gj){var _gk=E(_gj);if(!_gk._){return new T2(0,__Z,__Z);}else{var _gl=_gk.a;if(!B(A1(_gi,_gl))){return new T2(0,__Z,_gk);}else{var _gm=new T(function(){var _gn=_gh(_gi,_gk.b);return new T2(0,_gn.a,_gn.b);});return new T2(0,new T2(1,_gl,new T(function(){return E(E(_gm).a);})),new T(function(){return E(E(_gm).b);}));}}},_go=new T(function(){return unCStr("\n");}),_gp=function(_gq){return (E(_gq)==124)?false:true;},_gr=function(_gs,_gt){var _gu=_gh(_gp,unCStr(_gs)),_gv=_gu.a,_gw=function(_gx,_gy){var _gz=new T(function(){var _gA=new T(function(){return _R(_gt,new T(function(){return _R(_gy,_go);},1));});return unAppCStr(": ",_gA);},1);return _R(_gx,_gz);},_gB=E(_gu.b);if(!_gB._){return _gw(_gv,__Z);}else{if(E(_gB.a)==124){return _gw(_gv,new T2(1,32,_gB.b));}else{return _gw(_gv,__Z);}}},_gC=function(_gD){return _ge(new T1(0,new T(function(){return _gr(_gD,_ga);})),_g1);},_gE=new T(function(){return B(_gC("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_gF=function(_gG,_gH){var _gI=function(_gJ){var _gK=E(_gH);if(_gK._==3){return new T2(3,_gK.a,new T(function(){return _gF(_gG,_gK.b);}));}else{var _gL=E(_gG);if(_gL._==2){return _gK;}else{if(_gK._==2){return _gL;}else{var _gM=function(_gN){if(_gK._==4){var _gO=function(_gP){return new T1(4,new T(function(){return _R(_fE(_gL,_gP),_gK.a);}));};return new T1(1,_gO);}else{if(_gL._==1){var _gQ=_gL.a;if(!_gK._){return new T1(1,function(_gR){return _gF(B(A1(_gQ,_gR)),_gK);});}else{var _gS=function(_gT){return _gF(B(A1(_gQ,_gT)),new T(function(){return B(A1(_gK.a,_gT));}));};return new T1(1,_gS);}}else{if(!_gK._){return E(_gE);}else{var _gU=function(_gV){return _gF(_gL,new T(function(){return B(A1(_gK.a,_gV));}));};return new T1(1,_gU);}}}};switch(_gL._){case 1:if(_gK._==4){var _gW=function(_gX){return new T1(4,new T(function(){return _R(_fE(B(A1(_gL.a,_gX)),_gX),_gK.a);}));};return new T1(1,_gW);}else{return _gM(_);}break;case 4:var _gY=_gL.a;switch(_gK._){case 0:var _gZ=function(_h0){var _h1=new T(function(){return _R(_gY,new T(function(){return _fE(_gK,_h0);},1));});return new T1(4,_h1);};return new T1(1,_gZ);case 1:var _h2=function(_h3){var _h4=new T(function(){return _R(_gY,new T(function(){return _fE(B(A1(_gK.a,_h3)),_h3);},1));});return new T1(4,_h4);};return new T1(1,_h2);default:return new T1(4,new T(function(){return _R(_gY,_gK.a);}));}break;default:return _gM(_);}}}}},_h5=E(_gG);switch(_h5._){case 0:var _h6=E(_gH);if(!_h6._){var _h7=function(_h8){return _gF(B(A1(_h5.a,_h8)),new T(function(){return B(A1(_h6.a,_h8));}));};return new T1(0,_h7);}else{return _gI(_);}break;case 3:return new T2(3,_h5.a,new T(function(){return _gF(_h5.b,_gH);}));default:return _gI(_);}},_h9=new T(function(){return unCStr("(");}),_ha=new T(function(){return unCStr(")");}),_hb=new T2(0,function(_hc,_hd){return E(_hc)==E(_hd);},function(_he,_hf){return E(_he)!=E(_hf);}),_hg=function(_hh,_hi){while(1){var _hj=E(_hh);if(!_hj._){return (E(_hi)._==0)?true:false;}else{var _hk=E(_hi);if(!_hk._){return false;}else{if(E(_hj.a)!=E(_hk.a)){return false;}else{_hh=_hj.b;_hi=_hk.b;continue;}}}}},_hl=new T2(0,_hg,function(_hm,_hn){return (!_hg(_hm,_hn))?true:false;}),_ho=function(_hp,_hq){var _hr=E(_hp);switch(_hr._){case 0:return new T1(0,function(_hs){return C > 19 ? new F(function(){return _ho(B(A1(_hr.a,_hs)),_hq);}) : (++C,_ho(B(A1(_hr.a,_hs)),_hq));});case 1:return new T1(1,function(_ht){return C > 19 ? new F(function(){return _ho(B(A1(_hr.a,_ht)),_hq);}) : (++C,_ho(B(A1(_hr.a,_ht)),_hq));});case 2:return new T0(2);case 3:return _gF(B(A1(_hq,_hr.a)),new T(function(){return B(_ho(_hr.b,_hq));}));default:var _hu=function(_hv){var _hw=E(_hv);if(!_hw._){return __Z;}else{var _hx=E(_hw.a);return _R(_fE(B(A1(_hq,_hx.a)),_hx.b),new T(function(){return _hu(_hw.b);},1));}},_hy=_hu(_hr.a);return (_hy._==0)?new T0(2):new T1(4,_hy);}},_hz=new T0(2),_hA=function(_hB){return new T2(3,_hB,_hz);},_hC=function(_hD,_hE){var _hF=E(_hD);if(!_hF){return C > 19 ? new F(function(){return A1(_hE,0);}) : (++C,A1(_hE,0));}else{var _hG=new T(function(){return B(_hC(_hF-1|0,_hE));});return new T1(0,function(_hH){return E(_hG);});}},_hI=function(_hJ,_hK,_hL){var _hM=new T(function(){return B(A1(_hJ,_hA));}),_hN=function(_hO,_hP,_hQ,_hR){while(1){var _hS=B((function(_hT,_hU,_hV,_hW){var _hX=E(_hT);switch(_hX._){case 0:var _hY=E(_hU);if(!_hY._){return C > 19 ? new F(function(){return A1(_hK,_hW);}) : (++C,A1(_hK,_hW));}else{var _hZ=_hV+1|0,_i0=_hW;_hO=B(A1(_hX.a,_hY.a));_hP=_hY.b;_hQ=_hZ;_hR=_i0;return __continue;}break;case 1:var _i1=B(A1(_hX.a,_hU)),_i2=_hU,_hZ=_hV,_i0=_hW;_hO=_i1;_hP=_i2;_hQ=_hZ;_hR=_i0;return __continue;case 2:return C > 19 ? new F(function(){return A1(_hK,_hW);}) : (++C,A1(_hK,_hW));break;case 3:var _i3=new T(function(){return B(_ho(_hX,_hW));});return C > 19 ? new F(function(){return _hC(_hV,function(_i4){return E(_i3);});}) : (++C,_hC(_hV,function(_i4){return E(_i3);}));break;default:return C > 19 ? new F(function(){return _ho(_hX,_hW);}) : (++C,_ho(_hX,_hW));}})(_hO,_hP,_hQ,_hR));if(_hS!=__continue){return _hS;}}};return function(_i5){return _hN(_hM,_i5,0,_hL);};},_i6=function(_i7){return C > 19 ? new F(function(){return A1(_i7,__Z);}) : (++C,A1(_i7,__Z));},_i8=function(_i9,_ia){var _ib=function(_ic){var _id=E(_ic);if(!_id._){return _i6;}else{var _ie=_id.a;if(!B(A1(_i9,_ie))){return _i6;}else{var _if=new T(function(){return _ib(_id.b);}),_ig=function(_ih){var _ii=new T(function(){return B(A1(_if,function(_ij){return C > 19 ? new F(function(){return A1(_ih,new T2(1,_ie,_ij));}) : (++C,A1(_ih,new T2(1,_ie,_ij)));}));});return new T1(0,function(_ik){return E(_ii);});};return _ig;}}};return function(_il){return C > 19 ? new F(function(){return A2(_ib,_il,_ia);}) : (++C,A2(_ib,_il,_ia));};},_im=new T(function(){return err(new T(function(){return unCStr("valDig: Bad base");}));}),_in=function(_io,_ip){var _iq=function(_ir,_is){var _it=E(_ir);if(!_it._){var _iu=new T(function(){return B(A1(_is,__Z));});return function(_iv){return C > 19 ? new F(function(){return A1(_iv,_iu);}) : (++C,A1(_iv,_iu));};}else{var _iw=E(_it.a),_ix=function(_iy){var _iz=new T(function(){return _iq(_it.b,function(_iA){return C > 19 ? new F(function(){return A1(_is,new T2(1,_iy,_iA));}) : (++C,A1(_is,new T2(1,_iy,_iA)));});}),_iB=function(_iC){var _iD=new T(function(){return B(A1(_iz,_iC));});return new T1(0,function(_iE){return E(_iD);});};return _iB;};switch(E(_io)){case 8:if(48>_iw){var _iF=new T(function(){return B(A1(_is,__Z));});return function(_iG){return C > 19 ? new F(function(){return A1(_iG,_iF);}) : (++C,A1(_iG,_iF));};}else{if(_iw>55){var _iH=new T(function(){return B(A1(_is,__Z));});return function(_iI){return C > 19 ? new F(function(){return A1(_iI,_iH);}) : (++C,A1(_iI,_iH));};}else{return _ix(_iw-48|0);}}break;case 10:if(48>_iw){var _iJ=new T(function(){return B(A1(_is,__Z));});return function(_iK){return C > 19 ? new F(function(){return A1(_iK,_iJ);}) : (++C,A1(_iK,_iJ));};}else{if(_iw>57){var _iL=new T(function(){return B(A1(_is,__Z));});return function(_iM){return C > 19 ? new F(function(){return A1(_iM,_iL);}) : (++C,A1(_iM,_iL));};}else{return _ix(_iw-48|0);}}break;case 16:if(48>_iw){if(97>_iw){if(65>_iw){var _iN=new T(function(){return B(A1(_is,__Z));});return function(_iO){return C > 19 ? new F(function(){return A1(_iO,_iN);}) : (++C,A1(_iO,_iN));};}else{if(_iw>70){var _iP=new T(function(){return B(A1(_is,__Z));});return function(_iQ){return C > 19 ? new F(function(){return A1(_iQ,_iP);}) : (++C,A1(_iQ,_iP));};}else{return _ix((_iw-65|0)+10|0);}}}else{if(_iw>102){if(65>_iw){var _iR=new T(function(){return B(A1(_is,__Z));});return function(_iS){return C > 19 ? new F(function(){return A1(_iS,_iR);}) : (++C,A1(_iS,_iR));};}else{if(_iw>70){var _iT=new T(function(){return B(A1(_is,__Z));});return function(_iU){return C > 19 ? new F(function(){return A1(_iU,_iT);}) : (++C,A1(_iU,_iT));};}else{return _ix((_iw-65|0)+10|0);}}}else{return _ix((_iw-97|0)+10|0);}}}else{if(_iw>57){if(97>_iw){if(65>_iw){var _iV=new T(function(){return B(A1(_is,__Z));});return function(_iW){return C > 19 ? new F(function(){return A1(_iW,_iV);}) : (++C,A1(_iW,_iV));};}else{if(_iw>70){var _iX=new T(function(){return B(A1(_is,__Z));});return function(_iY){return C > 19 ? new F(function(){return A1(_iY,_iX);}) : (++C,A1(_iY,_iX));};}else{return _ix((_iw-65|0)+10|0);}}}else{if(_iw>102){if(65>_iw){var _iZ=new T(function(){return B(A1(_is,__Z));});return function(_j0){return C > 19 ? new F(function(){return A1(_j0,_iZ);}) : (++C,A1(_j0,_iZ));};}else{if(_iw>70){var _j1=new T(function(){return B(A1(_is,__Z));});return function(_j2){return C > 19 ? new F(function(){return A1(_j2,_j1);}) : (++C,A1(_j2,_j1));};}else{return _ix((_iw-65|0)+10|0);}}}else{return _ix((_iw-97|0)+10|0);}}}else{return _ix(_iw-48|0);}}break;default:return E(_im);}}},_j3=function(_j4){var _j5=E(_j4);if(!_j5._){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_ip,_j5);}) : (++C,A1(_ip,_j5));}};return function(_j6){return C > 19 ? new F(function(){return A3(_iq,_j6,_1,_j3);}) : (++C,A3(_iq,_j6,_1,_j3));};},_j7=function(_j8){var _j9=function(_ja){return C > 19 ? new F(function(){return A1(_j8,new T1(5,new T2(0,8,_ja)));}) : (++C,A1(_j8,new T1(5,new T2(0,8,_ja))));},_jb=function(_jc){return C > 19 ? new F(function(){return A1(_j8,new T1(5,new T2(0,16,_jc)));}) : (++C,A1(_j8,new T1(5,new T2(0,16,_jc))));},_jd=function(_je){switch(E(_je)){case 79:return new T1(1,_in(8,_j9));case 88:return new T1(1,_in(16,_jb));case 111:return new T1(1,_in(8,_j9));case 120:return new T1(1,_in(16,_jb));default:return new T0(2);}};return function(_jf){return (E(_jf)==48)?E(new T1(0,_jd)):new T0(2);};},_jg=function(_jh){return new T1(0,_j7(_jh));},_ji=function(_jj){return C > 19 ? new F(function(){return A1(_jj,__Z);}) : (++C,A1(_jj,__Z));},_jk=function(_jl){return C > 19 ? new F(function(){return A1(_jl,__Z);}) : (++C,A1(_jl,__Z));},_jm=function(_jn,_jo){while(1){var _jp=E(_jn);if(!_jp._){var _jq=_jp.a,_jr=E(_jo);if(!_jr._){var _js=_jr.a,_jt=addC(_jq,_js);if(!E(_jt.b)){return new T1(0,_jt.a);}else{_jn=new T1(1,I_fromInt(_jq));_jo=new T1(1,I_fromInt(_js));continue;}}else{_jn=new T1(1,I_fromInt(_jq));_jo=_jr;continue;}}else{var _ju=E(_jo);if(!_ju._){_jn=_jp;_jo=new T1(1,I_fromInt(_ju.a));continue;}else{return new T1(1,I_add(_jp.a,_ju.a));}}}},_jv=new T(function(){return _jm(new T1(0,2147483647),new T1(0,1));}),_jw=function(_jx){var _jy=E(_jx);if(!_jy._){var _jz=E(_jy.a);return (_jz==(-2147483648))?E(_jv):new T1(0, -_jz);}else{return new T1(1,I_negate(_jy.a));}},_jA=new T1(0,10),_jB=function(_jC,_jD){while(1){var _jE=E(_jC);if(!_jE._){return E(_jD);}else{var _jF=_jD+1|0;_jC=_jE.b;_jD=_jF;continue;}}},_jG=function(_jH){return new T1(0,_jH);},_jI=function(_jJ){return _jG(E(_jJ));},_jK=new T(function(){return err(new T(function(){return unCStr("this should not happen");}));}),_jL=function(_jM,_jN){while(1){var _jO=E(_jM);if(!_jO._){var _jP=_jO.a,_jQ=E(_jN);if(!_jQ._){var _jR=_jQ.a;if(!(imul(_jP,_jR)|0)){return new T1(0,imul(_jP,_jR)|0);}else{_jM=new T1(1,I_fromInt(_jP));_jN=new T1(1,I_fromInt(_jR));continue;}}else{_jM=new T1(1,I_fromInt(_jP));_jN=_jQ;continue;}}else{var _jS=E(_jN);if(!_jS._){_jM=_jO;_jN=new T1(1,I_fromInt(_jS.a));continue;}else{return new T1(1,I_mul(_jO.a,_jS.a));}}}},_jT=function(_jU,_jV){var _jW=E(_jV);if(!_jW._){return __Z;}else{var _jX=E(_jW.b);return (_jX._==0)?E(_jK):new T2(1,_jm(_jL(_jW.a,_jU),_jX.a),new T(function(){return _jT(_jU,_jX.b);}));}},_jY=new T1(0,0),_jZ=function(_k0,_k1,_k2){while(1){var _k3=(function(_k4,_k5,_k6){var _k7=E(_k6);if(!_k7._){return E(_jY);}else{if(!E(_k7.b)._){return E(_k7.a);}else{var _k8=E(_k5);if(_k8<=40){var _k9=function(_ka,_kb){while(1){var _kc=E(_kb);if(!_kc._){return E(_ka);}else{var _kd=_jm(_jL(_ka,_k4),_kc.a);_ka=_kd;_kb=_kc.b;continue;}}};return _k9(_jY,_k7);}else{var _ke=_jL(_k4,_k4);if(!(_k8%2)){var _kf=_jT(_k4,_k7);_k0=_ke;_k1=quot(_k8+1|0,2);_k2=_kf;return __continue;}else{var _kf=_jT(_k4,new T2(1,_jY,_k7));_k0=_ke;_k1=quot(_k8+1|0,2);_k2=_kf;return __continue;}}}}})(_k0,_k1,_k2);if(_k3!=__continue){return _k3;}}},_kg=function(_kh,_ki){return _jZ(_kh,new T(function(){return _jB(_ki,0);},1),_2m(_jI,_ki));},_kj=function(_kk){var _kl=new T(function(){var _km=new T(function(){var _kn=function(_ko){return C > 19 ? new F(function(){return A1(_kk,new T1(1,new T(function(){return _kg(_jA,_ko);})));}) : (++C,A1(_kk,new T1(1,new T(function(){return _kg(_jA,_ko);}))));};return new T1(1,_in(10,_kn));}),_kp=function(_kq){if(E(_kq)==43){var _kr=function(_ks){return C > 19 ? new F(function(){return A1(_kk,new T1(1,new T(function(){return _kg(_jA,_ks);})));}) : (++C,A1(_kk,new T1(1,new T(function(){return _kg(_jA,_ks);}))));};return new T1(1,_in(10,_kr));}else{return new T0(2);}},_kt=function(_ku){if(E(_ku)==45){var _kv=function(_kw){return C > 19 ? new F(function(){return A1(_kk,new T1(1,new T(function(){return _jw(_kg(_jA,_kw));})));}) : (++C,A1(_kk,new T1(1,new T(function(){return _jw(_kg(_jA,_kw));}))));};return new T1(1,_in(10,_kv));}else{return new T0(2);}};return _gF(_gF(new T1(0,_kt),new T1(0,_kp)),_km);});return _gF(new T1(0,function(_kx){return (E(_kx)==101)?E(_kl):new T0(2);}),new T1(0,function(_ky){return (E(_ky)==69)?E(_kl):new T0(2);}));},_kz=function(_kA){var _kB=function(_kC){return C > 19 ? new F(function(){return A1(_kA,new T1(1,_kC));}) : (++C,A1(_kA,new T1(1,_kC)));};return function(_kD){return (E(_kD)==46)?new T1(1,_in(10,_kB)):new T0(2);};},_kE=function(_kF){return new T1(0,_kz(_kF));},_kG=function(_kH){var _kI=function(_kJ){var _kK=function(_kL){return new T1(1,_hI(_kj,_ji,function(_kM){return C > 19 ? new F(function(){return A1(_kH,new T1(5,new T3(1,_kJ,_kL,_kM)));}) : (++C,A1(_kH,new T1(5,new T3(1,_kJ,_kL,_kM))));}));};return new T1(1,_hI(_kE,_jk,_kK));};return _in(10,_kI);},_kN=function(_kO){return new T1(1,_kG(_kO));},_kP=function(_kQ){return E(E(_kQ).a);},_kR=function(_kS,_kT,_kU){while(1){var _kV=E(_kU);if(!_kV._){return false;}else{if(!B(A3(_kP,_kS,_kT,_kV.a))){_kU=_kV.b;continue;}else{return true;}}}},_kW=new T(function(){return unCStr("!@#$%&*+./<=>?\\^|:-~");}),_kX=function(_kY){return _kR(_hb,_kY,_kW);},_kZ=function(_l0){var _l1=new T(function(){return B(A1(_l0,8));}),_l2=new T(function(){return B(A1(_l0,16));});return function(_l3){switch(E(_l3)){case 79:return E(_l1);case 88:return E(_l2);case 111:return E(_l1);case 120:return E(_l2);default:return new T0(2);}};},_l4=function(_l5){return new T1(0,_kZ(_l5));},_l6=function(_l7){return C > 19 ? new F(function(){return A1(_l7,10);}) : (++C,A1(_l7,10));},_l8=function(_l9){return err(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return _3q(9,_l9,__Z);})));},_la=function(_lb){var _lc=E(_lb);if(!_lc._){return E(_lc.a);}else{return I_toInt(_lc.a);}},_ld=function(_le,_lf){var _lg=E(_le);if(!_lg._){var _lh=_lg.a,_li=E(_lf);return (_li._==0)?_lh<=_li.a:I_compareInt(_li.a,_lh)>=0;}else{var _lj=_lg.a,_lk=E(_lf);return (_lk._==0)?I_compareInt(_lj,_lk.a)<=0:I_compare(_lj,_lk.a)<=0;}},_ll=function(_lm){return new T0(2);},_ln=function(_lo){var _lp=E(_lo);if(!_lp._){return _ll;}else{var _lq=_lp.a,_lr=E(_lp.b);if(!_lr._){return E(_lq);}else{var _ls=new T(function(){return _ln(_lr);}),_lt=function(_lu){return _gF(B(A1(_lq,_lu)),new T(function(){return B(A1(_ls,_lu));}));};return _lt;}}},_lv=function(_lw,_lx){var _ly=function(_lz,_lA,_lB){var _lC=E(_lz);if(!_lC._){return C > 19 ? new F(function(){return A1(_lB,_lw);}) : (++C,A1(_lB,_lw));}else{var _lD=E(_lA);if(!_lD._){return new T0(2);}else{if(E(_lC.a)!=E(_lD.a)){return new T0(2);}else{var _lE=new T(function(){return B(_ly(_lC.b,_lD.b,_lB));});return new T1(0,function(_lF){return E(_lE);});}}}};return function(_lG){return C > 19 ? new F(function(){return _ly(_lw,_lG,_lx);}) : (++C,_ly(_lw,_lG,_lx));};},_lH=new T(function(){return unCStr("SO");}),_lI=function(_lJ){var _lK=new T(function(){return B(A1(_lJ,14));});return new T1(1,_lv(_lH,function(_lL){return E(_lK);}));},_lM=new T(function(){return unCStr("SOH");}),_lN=function(_lO){var _lP=new T(function(){return B(A1(_lO,1));});return new T1(1,_lv(_lM,function(_lQ){return E(_lP);}));},_lR=new T(function(){return unCStr("NUL");}),_lS=function(_lT){var _lU=new T(function(){return B(A1(_lT,0));});return new T1(1,_lv(_lR,function(_lV){return E(_lU);}));},_lW=new T(function(){return unCStr("STX");}),_lX=function(_lY){var _lZ=new T(function(){return B(A1(_lY,2));});return new T1(1,_lv(_lW,function(_m0){return E(_lZ);}));},_m1=new T(function(){return unCStr("ETX");}),_m2=function(_m3){var _m4=new T(function(){return B(A1(_m3,3));});return new T1(1,_lv(_m1,function(_m5){return E(_m4);}));},_m6=new T(function(){return unCStr("EOT");}),_m7=function(_m8){var _m9=new T(function(){return B(A1(_m8,4));});return new T1(1,_lv(_m6,function(_ma){return E(_m9);}));},_mb=new T(function(){return unCStr("ENQ");}),_mc=function(_md){var _me=new T(function(){return B(A1(_md,5));});return new T1(1,_lv(_mb,function(_mf){return E(_me);}));},_mg=new T(function(){return unCStr("ACK");}),_mh=function(_mi){var _mj=new T(function(){return B(A1(_mi,6));});return new T1(1,_lv(_mg,function(_mk){return E(_mj);}));},_ml=new T(function(){return unCStr("BEL");}),_mm=function(_mn){var _mo=new T(function(){return B(A1(_mn,7));});return new T1(1,_lv(_ml,function(_mp){return E(_mo);}));},_mq=new T(function(){return unCStr("BS");}),_mr=function(_ms){var _mt=new T(function(){return B(A1(_ms,8));});return new T1(1,_lv(_mq,function(_mu){return E(_mt);}));},_mv=new T(function(){return unCStr("HT");}),_mw=function(_mx){var _my=new T(function(){return B(A1(_mx,9));});return new T1(1,_lv(_mv,function(_mz){return E(_my);}));},_mA=new T(function(){return unCStr("LF");}),_mB=function(_mC){var _mD=new T(function(){return B(A1(_mC,10));});return new T1(1,_lv(_mA,function(_mE){return E(_mD);}));},_mF=new T(function(){return unCStr("VT");}),_mG=function(_mH){var _mI=new T(function(){return B(A1(_mH,11));});return new T1(1,_lv(_mF,function(_mJ){return E(_mI);}));},_mK=new T(function(){return unCStr("FF");}),_mL=function(_mM){var _mN=new T(function(){return B(A1(_mM,12));});return new T1(1,_lv(_mK,function(_mO){return E(_mN);}));},_mP=new T(function(){return unCStr("CR");}),_mQ=function(_mR){var _mS=new T(function(){return B(A1(_mR,13));});return new T1(1,_lv(_mP,function(_mT){return E(_mS);}));},_mU=new T(function(){return unCStr("SI");}),_mV=function(_mW){var _mX=new T(function(){return B(A1(_mW,15));});return new T1(1,_lv(_mU,function(_mY){return E(_mX);}));},_mZ=new T(function(){return unCStr("DLE");}),_n0=function(_n1){var _n2=new T(function(){return B(A1(_n1,16));});return new T1(1,_lv(_mZ,function(_n3){return E(_n2);}));},_n4=new T(function(){return unCStr("DC1");}),_n5=function(_n6){var _n7=new T(function(){return B(A1(_n6,17));});return new T1(1,_lv(_n4,function(_n8){return E(_n7);}));},_n9=new T(function(){return unCStr("DC2");}),_na=function(_nb){var _nc=new T(function(){return B(A1(_nb,18));});return new T1(1,_lv(_n9,function(_nd){return E(_nc);}));},_ne=new T(function(){return unCStr("DC3");}),_nf=function(_ng){var _nh=new T(function(){return B(A1(_ng,19));});return new T1(1,_lv(_ne,function(_ni){return E(_nh);}));},_nj=new T(function(){return unCStr("DC4");}),_nk=function(_nl){var _nm=new T(function(){return B(A1(_nl,20));});return new T1(1,_lv(_nj,function(_nn){return E(_nm);}));},_no=new T(function(){return unCStr("NAK");}),_np=function(_nq){var _nr=new T(function(){return B(A1(_nq,21));});return new T1(1,_lv(_no,function(_ns){return E(_nr);}));},_nt=new T(function(){return unCStr("SYN");}),_nu=function(_nv){var _nw=new T(function(){return B(A1(_nv,22));});return new T1(1,_lv(_nt,function(_nx){return E(_nw);}));},_ny=new T(function(){return unCStr("ETB");}),_nz=function(_nA){var _nB=new T(function(){return B(A1(_nA,23));});return new T1(1,_lv(_ny,function(_nC){return E(_nB);}));},_nD=new T(function(){return unCStr("CAN");}),_nE=function(_nF){var _nG=new T(function(){return B(A1(_nF,24));});return new T1(1,_lv(_nD,function(_nH){return E(_nG);}));},_nI=new T(function(){return unCStr("EM");}),_nJ=function(_nK){var _nL=new T(function(){return B(A1(_nK,25));});return new T1(1,_lv(_nI,function(_nM){return E(_nL);}));},_nN=new T(function(){return unCStr("SUB");}),_nO=function(_nP){var _nQ=new T(function(){return B(A1(_nP,26));});return new T1(1,_lv(_nN,function(_nR){return E(_nQ);}));},_nS=new T(function(){return unCStr("ESC");}),_nT=function(_nU){var _nV=new T(function(){return B(A1(_nU,27));});return new T1(1,_lv(_nS,function(_nW){return E(_nV);}));},_nX=new T(function(){return unCStr("FS");}),_nY=function(_nZ){var _o0=new T(function(){return B(A1(_nZ,28));});return new T1(1,_lv(_nX,function(_o1){return E(_o0);}));},_o2=new T(function(){return unCStr("GS");}),_o3=function(_o4){var _o5=new T(function(){return B(A1(_o4,29));});return new T1(1,_lv(_o2,function(_o6){return E(_o5);}));},_o7=new T(function(){return unCStr("RS");}),_o8=function(_o9){var _oa=new T(function(){return B(A1(_o9,30));});return new T1(1,_lv(_o7,function(_ob){return E(_oa);}));},_oc=new T(function(){return unCStr("US");}),_od=function(_oe){var _of=new T(function(){return B(A1(_oe,31));});return new T1(1,_lv(_oc,function(_og){return E(_of);}));},_oh=new T(function(){return unCStr("SP");}),_oi=function(_oj){var _ok=new T(function(){return B(A1(_oj,32));});return new T1(1,_lv(_oh,function(_ol){return E(_ok);}));},_om=new T(function(){return unCStr("DEL");}),_on=function(_oo){var _op=new T(function(){return B(A1(_oo,127));});return new T1(1,_lv(_om,function(_oq){return E(_op);}));},_or=new T(function(){return _ln(new T2(1,function(_os){return new T1(1,_hI(_lN,_lI,_os));},new T2(1,_lS,new T2(1,_lX,new T2(1,_m2,new T2(1,_m7,new T2(1,_mc,new T2(1,_mh,new T2(1,_mm,new T2(1,_mr,new T2(1,_mw,new T2(1,_mB,new T2(1,_mG,new T2(1,_mL,new T2(1,_mQ,new T2(1,_mV,new T2(1,_n0,new T2(1,_n5,new T2(1,_na,new T2(1,_nf,new T2(1,_nk,new T2(1,_np,new T2(1,_nu,new T2(1,_nz,new T2(1,_nE,new T2(1,_nJ,new T2(1,_nO,new T2(1,_nT,new T2(1,_nY,new T2(1,_o3,new T2(1,_o8,new T2(1,_od,new T2(1,_oi,new T2(1,_on,__Z))))))))))))))))))))))))))))))))));}),_ot=function(_ou){var _ov=new T(function(){return B(A1(_ou,7));}),_ow=new T(function(){return B(A1(_ou,8));}),_ox=new T(function(){return B(A1(_ou,9));}),_oy=new T(function(){return B(A1(_ou,10));}),_oz=new T(function(){return B(A1(_ou,11));}),_oA=new T(function(){return B(A1(_ou,12));}),_oB=new T(function(){return B(A1(_ou,13));}),_oC=new T(function(){return B(A1(_ou,92));}),_oD=new T(function(){return B(A1(_ou,39));}),_oE=new T(function(){return B(A1(_ou,34));}),_oF=new T(function(){var _oG=function(_oH){var _oI=new T(function(){return _jG(E(_oH));}),_oJ=function(_oK){var _oL=_kg(_oI,_oK);if(!_ld(_oL,new T1(0,1114111))){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_ou,new T(function(){var _oM=_la(_oL);if(_oM>>>0>1114111){return _l8(_oM);}else{return _oM;}}));}) : (++C,A1(_ou,new T(function(){var _oM=_la(_oL);if(_oM>>>0>1114111){return _l8(_oM);}else{return _oM;}})));}};return new T1(1,_in(_oH,_oJ));},_oN=new T(function(){var _oO=new T(function(){return B(A1(_ou,31));}),_oP=new T(function(){return B(A1(_ou,30));}),_oQ=new T(function(){return B(A1(_ou,29));}),_oR=new T(function(){return B(A1(_ou,28));}),_oS=new T(function(){return B(A1(_ou,27));}),_oT=new T(function(){return B(A1(_ou,26));}),_oU=new T(function(){return B(A1(_ou,25));}),_oV=new T(function(){return B(A1(_ou,24));}),_oW=new T(function(){return B(A1(_ou,23));}),_oX=new T(function(){return B(A1(_ou,22));}),_oY=new T(function(){return B(A1(_ou,21));}),_oZ=new T(function(){return B(A1(_ou,20));}),_p0=new T(function(){return B(A1(_ou,19));}),_p1=new T(function(){return B(A1(_ou,18));}),_p2=new T(function(){return B(A1(_ou,17));}),_p3=new T(function(){return B(A1(_ou,16));}),_p4=new T(function(){return B(A1(_ou,15));}),_p5=new T(function(){return B(A1(_ou,14));}),_p6=new T(function(){return B(A1(_ou,6));}),_p7=new T(function(){return B(A1(_ou,5));}),_p8=new T(function(){return B(A1(_ou,4));}),_p9=new T(function(){return B(A1(_ou,3));}),_pa=new T(function(){return B(A1(_ou,2));}),_pb=new T(function(){return B(A1(_ou,1));}),_pc=new T(function(){return B(A1(_ou,0));}),_pd=function(_pe){switch(E(_pe)){case 64:return E(_pc);case 65:return E(_pb);case 66:return E(_pa);case 67:return E(_p9);case 68:return E(_p8);case 69:return E(_p7);case 70:return E(_p6);case 71:return E(_ov);case 72:return E(_ow);case 73:return E(_ox);case 74:return E(_oy);case 75:return E(_oz);case 76:return E(_oA);case 77:return E(_oB);case 78:return E(_p5);case 79:return E(_p4);case 80:return E(_p3);case 81:return E(_p2);case 82:return E(_p1);case 83:return E(_p0);case 84:return E(_oZ);case 85:return E(_oY);case 86:return E(_oX);case 87:return E(_oW);case 88:return E(_oV);case 89:return E(_oU);case 90:return E(_oT);case 91:return E(_oS);case 92:return E(_oR);case 93:return E(_oQ);case 94:return E(_oP);case 95:return E(_oO);default:return new T0(2);}};return _gF(new T1(0,function(_pf){return (E(_pf)==94)?E(new T1(0,_pd)):new T0(2);}),new T(function(){return B(A1(_or,_ou));}));});return _gF(new T1(1,_hI(_l4,_l6,_oG)),_oN);});return _gF(new T1(0,function(_pg){switch(E(_pg)){case 34:return E(_oE);case 39:return E(_oD);case 92:return E(_oC);case 97:return E(_ov);case 98:return E(_ow);case 102:return E(_oA);case 110:return E(_oy);case 114:return E(_oB);case 116:return E(_ox);case 118:return E(_oz);default:return new T0(2);}}),_oF);},_ph=function(_pi){return C > 19 ? new F(function(){return A1(_pi,0);}) : (++C,A1(_pi,0));},_pj=function(_pk){var _pl=E(_pk);if(!_pl._){return _ph;}else{var _pm=E(_pl.a),_pn=_pm>>>0,_po=new T(function(){return _pj(_pl.b);});if(_pn>887){var _pp=u_iswspace(_pm);if(!E(_pp)){return _ph;}else{var _pq=function(_pr){var _ps=new T(function(){return B(A1(_po,_pr));});return new T1(0,function(_pt){return E(_ps);});};return _pq;}}else{if(_pn==32){var _pu=function(_pv){var _pw=new T(function(){return B(A1(_po,_pv));});return new T1(0,function(_px){return E(_pw);});};return _pu;}else{if(_pn-9>>>0>4){if(_pn==160){var _py=function(_pz){var _pA=new T(function(){return B(A1(_po,_pz));});return new T1(0,function(_pB){return E(_pA);});};return _py;}else{return _ph;}}else{var _pC=function(_pD){var _pE=new T(function(){return B(A1(_po,_pD));});return new T1(0,function(_pF){return E(_pE);});};return _pC;}}}}},_pG=function(_pH){var _pI=new T(function(){return B(_pG(_pH));}),_pJ=function(_pK){return (E(_pK)==92)?E(_pI):new T0(2);},_pL=function(_pM){return E(new T1(0,_pJ));},_pN=new T1(1,function(_pO){return C > 19 ? new F(function(){return A2(_pj,_pO,_pL);}) : (++C,A2(_pj,_pO,_pL));}),_pP=new T(function(){return B(_ot(function(_pQ){return C > 19 ? new F(function(){return A1(_pH,new T2(0,_pQ,true));}) : (++C,A1(_pH,new T2(0,_pQ,true)));}));}),_pR=function(_pS){var _pT=E(_pS);if(_pT==38){return E(_pI);}else{var _pU=_pT>>>0;if(_pU>887){var _pV=u_iswspace(_pT);return (E(_pV)==0)?new T0(2):E(_pN);}else{return (_pU==32)?E(_pN):(_pU-9>>>0>4)?(_pU==160)?E(_pN):new T0(2):E(_pN);}}};return _gF(new T1(0,function(_pW){return (E(_pW)==92)?E(new T1(0,_pR)):new T0(2);}),new T1(0,function(_pX){var _pY=E(_pX);if(_pY==92){return E(_pP);}else{return C > 19 ? new F(function(){return A1(_pH,new T2(0,_pY,false));}) : (++C,A1(_pH,new T2(0,_pY,false)));}}));},_pZ=function(_q0,_q1){var _q2=new T(function(){return B(A1(_q1,new T1(1,new T(function(){return B(A1(_q0,__Z));}))));}),_q3=function(_q4){var _q5=E(_q4),_q6=E(_q5.a);if(_q6==34){if(!E(_q5.b)){return E(_q2);}else{return C > 19 ? new F(function(){return _pZ(function(_q7){return C > 19 ? new F(function(){return A1(_q0,new T2(1,_q6,_q7));}) : (++C,A1(_q0,new T2(1,_q6,_q7)));},_q1);}) : (++C,_pZ(function(_q7){return C > 19 ? new F(function(){return A1(_q0,new T2(1,_q6,_q7));}) : (++C,A1(_q0,new T2(1,_q6,_q7)));},_q1));}}else{return C > 19 ? new F(function(){return _pZ(function(_q8){return C > 19 ? new F(function(){return A1(_q0,new T2(1,_q6,_q8));}) : (++C,A1(_q0,new T2(1,_q6,_q8)));},_q1);}) : (++C,_pZ(function(_q8){return C > 19 ? new F(function(){return A1(_q0,new T2(1,_q6,_q8));}) : (++C,A1(_q0,new T2(1,_q6,_q8)));},_q1));}};return C > 19 ? new F(function(){return _pG(_q3);}) : (++C,_pG(_q3));},_q9=new T(function(){return unCStr("_\'");}),_qa=function(_qb){var _qc=u_iswalnum(_qb);if(!E(_qc)){return _kR(_hb,_qb,_q9);}else{return true;}},_qd=function(_qe){return _qa(E(_qe));},_qf=new T(function(){return unCStr(",;()[]{}`");}),_qg=new T(function(){return unCStr("=>");}),_qh=new T(function(){return unCStr("~");}),_qi=new T(function(){return unCStr("@");}),_qj=new T(function(){return unCStr("->");}),_qk=new T(function(){return unCStr("<-");}),_ql=new T(function(){return unCStr("|");}),_qm=new T(function(){return unCStr("\\");}),_qn=new T(function(){return unCStr("=");}),_qo=new T(function(){return unCStr("::");}),_qp=new T(function(){return unCStr("..");}),_qq=function(_qr){var _qs=new T(function(){return B(A1(_qr,new T0(6)));}),_qt=new T(function(){var _qu=new T(function(){var _qv=function(_qw){var _qx=new T(function(){return B(A1(_qr,new T1(0,_qw)));});return new T1(0,function(_qy){return (E(_qy)==39)?E(_qx):new T0(2);});};return B(_ot(_qv));}),_qz=function(_qA){var _qB=E(_qA);switch(_qB){case 39:return new T0(2);case 92:return E(_qu);default:var _qC=new T(function(){return B(A1(_qr,new T1(0,_qB)));});return new T1(0,function(_qD){return (E(_qD)==39)?E(_qC):new T0(2);});}},_qE=new T(function(){var _qF=new T(function(){return B(_pZ(_1,_qr));}),_qG=new T(function(){var _qH=new T(function(){var _qI=new T(function(){var _qJ=function(_qK){var _qL=E(_qK),_qM=u_iswalpha(_qL);return (E(_qM)==0)?(_qL==95)?new T1(1,_i8(_qd,function(_qN){return C > 19 ? new F(function(){return A1(_qr,new T1(3,new T2(1,_qL,_qN)));}) : (++C,A1(_qr,new T1(3,new T2(1,_qL,_qN))));})):new T0(2):new T1(1,_i8(_qd,function(_qO){return C > 19 ? new F(function(){return A1(_qr,new T1(3,new T2(1,_qL,_qO)));}) : (++C,A1(_qr,new T1(3,new T2(1,_qL,_qO))));}));};return _gF(new T1(0,_qJ),new T(function(){return new T1(1,_hI(_jg,_kN,_qr));}));}),_qP=function(_qQ){return (!_kR(_hb,_qQ,_kW))?new T0(2):new T1(1,_i8(_kX,function(_qR){var _qS=new T2(1,_qQ,_qR);if(!_kR(_hl,_qS,new T2(1,_qp,new T2(1,_qo,new T2(1,_qn,new T2(1,_qm,new T2(1,_ql,new T2(1,_qk,new T2(1,_qj,new T2(1,_qi,new T2(1,_qh,new T2(1,_qg,__Z)))))))))))){return C > 19 ? new F(function(){return A1(_qr,new T1(4,_qS));}) : (++C,A1(_qr,new T1(4,_qS)));}else{return C > 19 ? new F(function(){return A1(_qr,new T1(2,_qS));}) : (++C,A1(_qr,new T1(2,_qS)));}}));};return _gF(new T1(0,_qP),_qI);});return _gF(new T1(0,function(_qT){if(!_kR(_hb,_qT,_qf)){return new T0(2);}else{return C > 19 ? new F(function(){return A1(_qr,new T1(2,new T2(1,_qT,__Z)));}) : (++C,A1(_qr,new T1(2,new T2(1,_qT,__Z))));}}),_qH);});return _gF(new T1(0,function(_qU){return (E(_qU)==34)?E(_qF):new T0(2);}),_qG);});return _gF(new T1(0,function(_qV){return (E(_qV)==39)?E(new T1(0,_qz)):new T0(2);}),_qE);});return _gF(new T1(1,function(_qW){return (E(_qW)._==0)?E(_qs):new T0(2);}),_qt);},_qX=function(_qY,_qZ){var _r0=new T(function(){var _r1=new T(function(){var _r2=function(_r3){var _r4=new T(function(){var _r5=new T(function(){return B(A1(_qZ,_r3));});return B(_qq(function(_r6){var _r7=E(_r6);return (_r7._==2)?(!_aH(_r7.a,_ha))?new T0(2):E(_r5):new T0(2);}));}),_r8=function(_r9){return E(_r4);};return new T1(1,function(_ra){return C > 19 ? new F(function(){return A2(_pj,_ra,_r8);}) : (++C,A2(_pj,_ra,_r8));});};return B(A2(_qY,0,_r2));});return B(_qq(function(_rb){var _rc=E(_rb);return (_rc._==2)?(!_aH(_rc.a,_h9))?new T0(2):E(_r1):new T0(2);}));}),_rd=function(_re){return E(_r0);};return function(_rf){return C > 19 ? new F(function(){return A2(_pj,_rf,_rd);}) : (++C,A2(_pj,_rf,_rd));};},_rg=function(_rh,_ri){var _rj=function(_rk){var _rl=new T(function(){return B(A1(_rh,_rk));}),_rm=function(_rn){return _gF(B(A1(_rl,_rn)),new T(function(){return new T1(1,_qX(_rj,_rn));}));};return _rm;},_ro=new T(function(){return B(A1(_rh,_ri));}),_rp=function(_rq){return _gF(B(A1(_ro,_rq)),new T(function(){return new T1(1,_qX(_rj,_rq));}));};return _rp;},_rr=function(_rs,_rt){var _ru=function(_rv,_rw){var _rx=function(_ry){return C > 19 ? new F(function(){return A1(_rw,new T(function(){return  -E(_ry);}));}) : (++C,A1(_rw,new T(function(){return  -E(_ry);})));},_rz=new T(function(){return B(_qq(function(_rA){return C > 19 ? new F(function(){return A3(_rs,_rA,_rv,_rx);}) : (++C,A3(_rs,_rA,_rv,_rx));}));}),_rB=function(_rC){return E(_rz);},_rD=function(_rE){return C > 19 ? new F(function(){return A2(_pj,_rE,_rB);}) : (++C,A2(_pj,_rE,_rB));},_rF=new T(function(){return B(_qq(function(_rG){var _rH=E(_rG);if(_rH._==4){var _rI=E(_rH.a);if(!_rI._){return C > 19 ? new F(function(){return A3(_rs,_rH,_rv,_rw);}) : (++C,A3(_rs,_rH,_rv,_rw));}else{if(E(_rI.a)==45){if(!E(_rI.b)._){return E(new T1(1,_rD));}else{return C > 19 ? new F(function(){return A3(_rs,_rH,_rv,_rw);}) : (++C,A3(_rs,_rH,_rv,_rw));}}else{return C > 19 ? new F(function(){return A3(_rs,_rH,_rv,_rw);}) : (++C,A3(_rs,_rH,_rv,_rw));}}}else{return C > 19 ? new F(function(){return A3(_rs,_rH,_rv,_rw);}) : (++C,A3(_rs,_rH,_rv,_rw));}}));}),_rJ=function(_rK){return E(_rF);};return new T1(1,function(_rL){return C > 19 ? new F(function(){return A2(_pj,_rL,_rJ);}) : (++C,A2(_pj,_rL,_rJ));});};return _rg(_ru,_rt);},_rM=function(_rN){var _rO=E(_rN);if(!_rO._){var _rP=_rO.b,_rQ=new T(function(){return _jZ(new T(function(){return _jG(E(_rO.a));}),new T(function(){return _jB(_rP,0);},1),_2m(_jI,_rP));});return new T1(1,_rQ);}else{return (E(_rO.b)._==0)?(E(_rO.c)._==0)?new T1(1,new T(function(){return _kg(_jA,_rO.a);})):__Z:__Z;}},_rR=function(_rS,_rT){return new T0(2);},_rU=function(_rV){var _rW=E(_rV);if(_rW._==5){var _rX=_rM(_rW.a);if(!_rX._){return _rR;}else{var _rY=new T(function(){return _la(_rX.a);});return function(_rZ,_s0){return C > 19 ? new F(function(){return A1(_s0,_rY);}) : (++C,A1(_s0,_rY));};}}else{return _rR;}},_s1=function(_s2){var _s3=function(_s4){return E(new T2(3,_s2,_hz));};return new T1(1,function(_s5){return C > 19 ? new F(function(){return A2(_pj,_s5,_s3);}) : (++C,A2(_pj,_s5,_s3));});},_s6=new T(function(){return B(A3(_rr,_rU,0,_s1));}),_s7=function(_s8,_s9){var _sa=E(_s8);switch(_sa._){case 1:return new T3(1,_sa.a,_s9,_sa.c);case 2:return new T3(2,_sa.a,_s9,_sa.c);case 3:return new T3(3,_sa.a,_s9,_sa.c);case 4:return new T4(4,_sa.a,new T(function(){var _sb=_fx(_fE(_s6,_s9));if(!_sb._){return __Z;}else{if(!E(_sb.b)._){return new T1(1,_sb.a);}else{return __Z;}}}),_sa.c,_sa.d);case 5:var _sc=new T(function(){return _2m(function(_sd){var _se=E(_sd);if(!_se._){var _sf=E(_se.a);return (_sf._==0)?(!_aH(_sf.a,_s9))?new T2(0,_sf,false):new T2(0,_sf,true):(!_aH(_sf.b,_s9))?new T2(0,_sf,false):new T2(0,_sf,true);}else{var _sg=_se.c,_sh=E(_se.a);return (_sh._==0)?(!_aH(_sh.a,_s9))?new T3(1,_sh,false,_sg):new T3(1,_sh,true,_sg):(!_aH(_sh.b,_s9))?new T3(1,_sh,false,_sg):new T3(1,_sh,true,_sg);}},_sa.b);});return new T3(5,_sa.a,_sc,_sa.c);case 6:return new T3(6,_sa.a,new T(function(){if(!_aH(_s9,__Z)){return new T1(1,_s9);}else{return __Z;}}),_sa.c);default:return _sa;}},_si=function(_sj,_){var _sk=E(_sj);switch(_sk._){case 0:var _sl=_fO(_3Y(_3C(_sk.a).b),_),_sm=E(_3d)(E(_sl));return new T(function(){return _s7(_sk,new T(function(){var _sn=String(_sm);return fromJSStr(_sn);}));});case 1:var _so=_fO(_3Y(_3C(_sk.a).b),_),_sp=E(_3d)(E(_so));return new T(function(){return _s7(_sk,new T(function(){var _sq=String(_sp);return fromJSStr(_sq);}));});case 2:var _sr=_fO(_3Y(_3C(_sk.a).b),_),_ss=E(_3d)(E(_sr));return new T(function(){return _s7(_sk,new T(function(){var _st=String(_ss);return fromJSStr(_st);}));});case 3:var _su=_fO(_3Y(_3C(_sk.a).b),_),_sv=E(_3d)(E(_su));return new T(function(){return _s7(_sk,new T(function(){var _sw=String(_sv);return fromJSStr(_sw);}));});case 4:var _sx=_sk.a,_sy=_sk.d,_sz=_3C(_sx).b,_sA=_fO(_3Y(_sz),_),_sB=E(_3d)(E(_sA)),_sC=_fp(new T(function(){return _R(_3Y(_sz),_fw);},1),_);return new T(function(){var _sD=new T(function(){var _sE=String(_sB);return fromJSStr(_sE);}),_sF=function(_sG){return new T4(4,_sx,new T(function(){var _sH=_fx(_fE(_s6,_sD));if(!_sH._){return __Z;}else{if(!E(_sH.b)._){return new T1(1,_sH.a);}else{return __Z;}}}),__Z,_sy);};if(!_aH(_sC,_fv)){var _sI=E(_sC);if(!_sI._){return _sF(_);}else{return new T4(4,_sx,new T(function(){var _sJ=_fx(_fE(_s6,_sD));if(!_sJ._){return __Z;}else{if(!E(_sJ.b)._){return new T1(1,_sJ.a);}else{return __Z;}}}),new T1(1,_sI),_sy);}}else{return _sF(_);}});case 5:var _sK=_fO(_3Y(_3C(_sk.a).b),_),_sL=E(_3d)(E(_sK));return new T(function(){return _s7(_sk,new T(function(){var _sM=String(_sL);return fromJSStr(_sM);}));});case 6:var _sN=_fO(_3Y(_3C(_sk.a).b),_),_sO=E(_3d)(E(_sN));return new T(function(){return _s7(_sk,new T(function(){var _sP=String(_sO);return fromJSStr(_sP);}));});case 7:var _sQ=_fO(_3Y(_3C(_sk.a).b),_),_sR=E(_3d)(E(_sQ));return new T(function(){return _s7(_sk,new T(function(){var _sS=String(_sR);return fromJSStr(_sS);}));});case 8:var _sT=_fO(_3Y(_3C(_sk.a).b),_),_sU=E(_3d)(E(_sT));return new T(function(){return _s7(_sk,new T(function(){var _sV=String(_sU);return fromJSStr(_sV);}));});case 9:var _sW=_fO(_3Y(_3C(_sk.a).b),_),_sX=E(_3d)(E(_sW));return new T(function(){return _s7(_sk,new T(function(){var _sY=String(_sX);return fromJSStr(_sY);}));});case 10:var _sZ=_fO(_3Y(_3C(_sk.a).b),_),_t0=E(_3d)(E(_sZ));return new T(function(){return _s7(_sk,new T(function(){var _t1=String(_t0);return fromJSStr(_t1);}));});default:var _t2=_fO(_3Y(_3C(_sk.a).b),_),_t3=E(_3d)(E(_t2));return new T(function(){return _s7(_sk,new T(function(){var _t4=String(_t3);return fromJSStr(_t4);}));});}},_t5=new T(function(){return unCStr(" does not exist");}),_t6=function(_t7,_t8,_){var _t9=B(_fe(_t7,_t8));if(!_t9._){var _ta=new T(function(){return _R(new T2(1,34,new T(function(){return _ex(_t7,new T2(1,34,__Z));})),_t5);}),_tb=_4T(unAppCStr("identity2elementUpdated: element with identity=",_ta),_);return __Z;}else{var _tc=_si(_t9.a,_);return new T1(1,_tc);}},_td=function(_te,_tf,_){var _tg=(function (val, jq) { jq.val(val).change(); return jq; });return _tg(toJSStr(E(_te)),_tf);},_th=new T(function(){return unCStr("RecSelError");}),_ti=function(_tj){return E(new T5(0,new Long(2975920724,3651309139,true),new Long(465443624,4160253997,true),new T5(0,new Long(2975920724,3651309139,true),new Long(465443624,4160253997,true),_fR,_fS,_th),__Z,__Z));},_tk=function(_tl){return E(E(_tl).a);},_tm=function(_tn,_to){return _R(E(_tn).a,_to);},_tp=new T(function(){return new T5(0,_ti,new T3(0,function(_tq,_tr,_ts){return _R(E(_tr).a,_ts);},_tk,function(_tt,_tu){return _1K(_tm,_tt,_tu);}),function(_g7){return new T2(0,_tp,_g7);},function(_tv){var _tw=E(_tv);return _G(_E(_tw.a),_ti,_tw.b);},_tk);}),_tx=function(_ty){var _tz=new T(function(){return unAppCStr("No match in record selector ",new T(function(){return unCStr(_ty);}));});return _ge(new T1(0,_tz),_tp);},_tA=new T(function(){return B(_tx("neMaybeValue"));}),_tB=function(_tC,_tD){while(1){var _tE=E(_tC);if(!_tE._){return E(_tD);}else{var _tF=_tE.b,_tG=E(_tE.a);if(_tG._==4){var _tH=E(_tG.b);if(!_tH._){_tC=_tF;continue;}else{var _tI=_tD+E(_tH.a)|0;_tC=_tF;_tD=_tI;continue;}}else{return E(_tA);}}}},_tJ=function(_tK){return E(_tK);},_tL=new T(function(){return unCStr("TB");}),_tM=new T(function(){return unCStr("PB");}),_tN=new T(function(){return unCStr("MB");}),_tO=new T(function(){return unCStr("GB");}),_tP=function(_tQ){var _tR=E(_tQ);if(_tR._==4){var _tS=_tR.b,_tT=E(_tR.c);if(!_tT._){return __Z;}else{var _tU=_tT.a;if(!_aH(_tU,_tO)){if(!_aH(_tU,_tN)){if(!_aH(_tU,_tM)){if(!_aH(_tU,_tL)){return __Z;}else{var _tV=E(_tS);return (_tV._==0)?__Z:new T1(1,new T(function(){return _tJ(_tV.a);}));}}else{var _tW=E(_tS);return (_tW._==0)?__Z:new T1(1,new T(function(){return E(_tW.a)*1000;}));}}else{var _tX=E(_tS);return (_tX._==0)?__Z:new T1(1,new T(function(){return E(_tX.a)*1.0e-6;}));}}else{var _tY=E(_tS);return (_tY._==0)?__Z:new T1(1,new T(function(){return E(_tY.a)*1.0e-3;}));}}}else{return __Z;}},_tZ=function(_u0,_u1){while(1){var _u2=E(_u0);if(!_u2._){return E(_u1);}else{var _u3=_u2.b,_u4=_tP(_u2.a);if(!_u4._){_u0=_u3;continue;}else{var _u5=_u1+E(_u4.a);_u0=_u3;_u1=_u5;continue;}}}},_u6=new T(function(){return unCStr("true");}),_u7=new T(function(){return unCStr("readonly");}),_u8=new T(function(){return unCStr("#eee");}),_u9=new T(function(){return unCStr("background-color");}),_ua=function(_ub){return _3Y(_3C(_3F(_ub)).b);},_uc=function(_ud){while(1){var _ue=E(_ud);if(!_ue._){return false;}else{if(!E(_ue.a)._){return true;}else{_ud=_ue.b;continue;}}}},_uf=function(_ug){while(1){var _uh=E(_ug);if(!_uh._){return false;}else{if(!E(_uh.a)._){return true;}else{_ug=_uh.b;continue;}}}},_ui=function(_uj,_uk,_){var _ul=(function (elId, context) { return $(elId, context); });return _ul(toJSStr(E(_uj)),_uk);},_um=new T(function(){return unCStr("_flagPlaceId");}),_un=function(_uo){return _R(_3Y(_3C(_3F(_uo)).b),_um);},_up=new T(function(){return unCStr(".validity-flag");}),_uq=new T(function(){return unCStr("#");}),_ur=function(_us){return E(E(_us).c);},_ut=new T(function(){return (function (jq) { var p = jq.parent(); jq.remove(); return p; });}),_uu=function(_uv){return E(E(_uv).b);},_uw=function(_ux,_uy,_uz,_){var _uA=_4b(_R(_uq,new T(function(){return _un(_ux);},1)),_),_uB=E(_uA),_uC=_ui(_up,_uB,_),_uD=E(_ut)(E(_uC));if(!E(_uz)){if(!E(_3C(_3F(_ux)).h)){return 0;}else{var _uE=_a1(_ur(_uy),_uB,_);return 0;}}else{if(!E(_3C(_3F(_ux)).h)){return 0;}else{var _uF=_a1(_uu(_uy),_uB,_);return 0;}}},_uG=new T(function(){return unCStr("Rule application did not unify: ");}),_uH=new T(function(){return unCStr(" @");}),_uI=new T(function(){return unCStr("invalid operand in ");}),_uJ=function(_uK,_){var _uL=(function (identity) { return $('[identity="' + identity + '"]'); });return _uL(toJSStr(E(_uK)));},_uM=function(_uN,_uO,_uP,_){var _uQ=function(_){var _uR=E(_uP);switch(_uR._){case 2:var _uS=_uJ(_uR.a,_),_uT=E(_3d)(E(_uS)),_uU=_uJ(_uR.b,_),_uV=String(_uT),_uW=_td(fromJSStr(_uV),E(_uU),_);return 0;case 3:var _uX=_fO(B(_ua(_uN)),_),_uY=E(_uX),_uZ=_3h(_u9,_u8,_uY,_),_v0=_9F(_u7,_u6,_uY,_);return 0;case 4:var _v1=_si(_uN,_),_v2=E(_v1);if(_v2._==4){var _v3=E(_v2.b);if(!_v3._){return _uw(_v2,_uO,false,_);}else{return _uw(_v2,_uO,new T(function(){return B(A1(_uR.a,_v3.a));},1),_);}}else{return E(_tA);}break;default:var _v4=new T(function(){var _v5=new T(function(){return _R(_uH,new T(function(){return _dn(_uN);},1));},1);return _R(_f5(_uR),_v5);},1);return _4T(_R(_uG,_v4),_);}};if(E(_uN)._==4){var _v6=E(_uP);switch(_v6._){case 0:var _v7=function(_,_v8){if(!_uc(_v8)){var _v9=_uJ(_v6.b,_),_va=_td(_3q(0,_tB(_4M(_v8),0),__Z),E(_v9),_);return 0;}else{var _vb=_4T(_R(_uI,new T(function(){return _f5(_v6);},1)),_);return 0;}},_vc=E(_v6.a);if(!_vc._){return _v7(_,__Z);}else{var _vd=E(_uO).a,_ve=_t6(_vc.a,_vd,_),_vf=function(_vg,_){var _vh=E(_vg);if(!_vh._){return __Z;}else{var _vi=_t6(_vh.a,_vd,_),_vj=_vf(_vh.b,_);return new T2(1,_vi,_vj);}},_vk=_vf(_vc.b,_);return _v7(_,new T2(1,_ve,_vk));}break;case 1:var _vl=function(_,_vm){if(!_uf(_vm)){var _vn=_uJ(_v6.b,_),_vo=jsShow(_tZ(_4M(_vm),0)),_vp=_td(fromJSStr(_vo),E(_vn),_);return 0;}else{return 0;}},_vq=E(_v6.a);if(!_vq._){return _vl(_,__Z);}else{var _vr=E(_uO).a,_vs=_t6(_vq.a,_vr,_),_vt=function(_vu,_){var _vv=E(_vu);if(!_vv._){return __Z;}else{var _vw=_t6(_vv.a,_vr,_),_vx=_vt(_vv.b,_);return new T2(1,_vw,_vx);}},_vy=_vt(_vq.b,_);return _vl(_,new T2(1,_vs,_vy));}break;default:return _uQ(_);}}else{return _uQ(_);}},_vz=function(_vA,_vB,_){var _vC=function(_vD,_){while(1){var _vE=E(_vD);if(!_vE._){return 0;}else{var _vF=_uM(_vA,_vB,_vE.a,_);_vD=_vE.b;continue;}}};return _vC(_3C(_3F(_vA)).i,_);},_vG=function(_vH){return (E(_vH)._==0)?false:true;},_vI=new T(function(){return B(_tx("nfiUnit"));}),_vJ=function(_vK){while(1){var _vL=E(_vK);if(!_vL._){return true;}else{if(!E(_vL.a)){return false;}else{_vK=_vL.b;continue;}}}},_vM=function(_vN){while(1){var _vO=E(_vN);if(!_vO._){return false;}else{var _vP=_vO.b,_vQ=E(_vO.a);if(!_vQ._){if(!E(_vQ.b)){_vN=_vP;continue;}else{return true;}}else{if(!E(_vQ.b)){_vN=_vP;continue;}else{return true;}}}}},_vR=function(_vS){while(1){var _vT=E(_vS);if(!_vT._){return true;}else{if(!E(_vT.a)){return false;}else{_vS=_vT.b;continue;}}}},_vU=function(_vV){while(1){var _vW=(function(_vX){var _vY=E(_vX);if(!_vY._){return __Z;}else{var _vZ=_vY.b,_w0=E(_vY.a);switch(_w0._){case 0:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){return _w1(_w0.b);}),new T(function(){return _vU(_vZ);}));}break;case 1:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){if(!_hg(_w0.b,__Z)){return true;}else{return false;}}),new T(function(){return _vU(_vZ);}));}break;case 2:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){if(!_hg(_w0.b,__Z)){return true;}else{return false;}}),new T(function(){return _vU(_vZ);}));}break;case 3:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){if(!_hg(_w0.b,__Z)){return true;}else{return false;}}),new T(function(){return _vU(_vZ);}));}break;case 4:var _w2=_w0.a;if(!E(_3C(_w2).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){var _w3=E(_w0.b);if(!_w3._){return false;}else{if(E(_w3.a)<0){return false;}else{var _w4=E(_w2);if(_w4._==3){if(E(_w4.b)._==1){return _vG(_w0.c);}else{return true;}}else{return E(_vI);}}}}),new T(function(){return _vU(_vZ);}));}break;case 5:var _w5=_w0.a,_w6=_w0.b;if(!E(_3C(_w5).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){if(!E(_3C(_w5).h)){return _vR(_2m(_w7,_w6));}else{if(!_vM(_w6)){return false;}else{return _vR(_2m(_w7,_w6));}}}),new T(function(){return _vU(_vZ);}));}break;case 6:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){return _vG(_w0.b);}),new T(function(){return _vU(_vZ);}));}break;case 7:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){return _w1(_w0.b);}),new T(function(){return _vU(_vZ);}));}break;case 8:return new T2(1,new T(function(){if(!E(_w0.b)){return true;}else{return _w1(_w0.c);}}),new T(function(){return _vU(_vZ);}));case 9:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,new T(function(){return _w1(_w0.b);}),new T(function(){return _vU(_vZ);}));}break;case 10:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,true,new T(function(){return _vU(_vZ);}));}break;default:if(!E(_3C(_w0.a).h)){_vV=_vZ;return __continue;}else{return new T2(1,true,new T(function(){return _vU(_vZ);}));}}}})(_vV);if(_vW!=__continue){return _vW;}}},_w1=function(_w8){return _vJ(_vU(_w8));},_w7=function(_w9){var _wa=E(_w9);if(!_wa._){return true;}else{return _w1(_wa.c);}},_wb=function(_wc){var _wd=E(_wc);switch(_wd._){case 0:return _w1(_wd.b);case 1:return (!_hg(_wd.b,__Z))?true:false;case 2:return (!_hg(_wd.b,__Z))?true:false;case 3:return (!_hg(_wd.b,__Z))?true:false;case 4:var _we=E(_wd.b);if(!_we._){return false;}else{if(E(_we.a)<0){return false;}else{var _wf=E(_wd.a);if(_wf._==3){if(E(_wf.b)._==1){return _vG(_wd.c);}else{return true;}}else{return E(_vI);}}}break;case 5:var _wg=_wd.b;if(!E(_3C(_wd.a).h)){return _vR(_2m(_w7,_wg));}else{if(!_vM(_wg)){return false;}else{return _vR(_2m(_w7,_wg));}}break;case 6:return _vG(_wd.b);case 7:return _w1(_wd.b);case 8:if(!E(_wd.b)){return true;}else{return _w1(_wd.c);}break;case 9:return _w1(_wd.b);case 10:return true;default:return true;}},_wh=function(_wi,_wj,_wk,_){var _wl=_si(_wi,_),_wm=_uw(_wl,_wj,new T(function(){return _wb(_wl);},1),_),_wn=_vz(_wi,_wj,_);return C > 19 ? new F(function(){return A3(E(_wk).b,_wi,_wj,_);}) : (++C,A3(E(_wk).b,_wi,_wj,_));},_wo=function(_wp,_wq,_wr,_){var _ws=_si(_wp,_),_wt=_uw(_ws,_wq,new T(function(){return _wb(_ws);},1),_),_wu=_vz(_wp,_wq,_);return C > 19 ? new F(function(){return A3(E(_wr).a,_wp,_wq,_);}) : (++C,A3(E(_wr).a,_wp,_wq,_));},_wv=function(_ww,_wx,_){var _wy=E(_9M)(_wx),_wz=E(_9L)(_wy),_wA=(function (cls, jq) { jq.addClass(cls); return jq; }),_wB=_wA(toJSStr(E(_ww)),_wz);return C > 19 ? new F(function(){return E(_9K)(_wB);}) : (++C,E(_9K)(_wB));},_wC=function(_wD,_wE,_){var _wF=__createJSFunc(2,function(_wG,_){var _wH=B(A2(E(_wD),_wG,_));return _2D;}),_wI=E(_wE),_wJ=(function (ev, jq) { jq.blur(ev); }),_wK=_wJ(_wF,_wI);return _wI;},_wL=function(_wM,_wN,_){var _wO=E(_9M)(_wN),_wP=E(_9L)(_wO),_wQ=_wC(_wM,_wP,_);return C > 19 ? new F(function(){return E(_9K)(E(_wQ));}) : (++C,E(_9K)(E(_wQ)));},_wR=function(_wS,_wT,_){var _wU=__createJSFunc(2,function(_wV,_){var _wW=B(A2(E(_wS),_wV,_));return _2D;}),_wX=E(_wT),_wY=(function (ev, jq) { jq.change(ev); }),_wZ=_wY(_wU,_wX);return _wX;},_x0=function(_x1,_x2,_){var _x3=E(_9M)(_x2),_x4=E(_9L)(_x3),_x5=_wR(_x1,_x4,_);return C > 19 ? new F(function(){return E(_9K)(E(_x5));}) : (++C,E(_9K)(E(_x5)));},_x6=function(_x7,_x8,_){var _x9=E(_9M)(_x8),_xa=E(_9L)(_x9),_xb=_an(_x7,_xa,_);return C > 19 ? new F(function(){return E(_9K)(E(_xb));}) : (++C,E(_9K)(E(_xb)));},_xc=function(_xd,_xe,_){var _xf=__createJSFunc(2,function(_xg,_){var _xh=B(A2(E(_xd),_xg,_));return _2D;}),_xi=E(_xe),_xj=(function (ev, jq) { jq.keyup(ev); }),_xk=_xj(_xf,_xi);return _xi;},_xl=function(_xm,_xn,_){var _xo=E(_9M)(_xn),_xp=E(_9L)(_xo),_xq=_xc(_xm,_xp,_);return C > 19 ? new F(function(){return E(_9K)(E(_xq));}) : (++C,E(_9K)(E(_xq)));},_xr=function(_xs,_xt,_){var _xu=__createJSFunc(2,function(_xv,_){var _xw=B(A2(E(_xs),_xv,_));return _2D;}),_xx=E(_xt),_xy=(function (ev, jq) { jq.mouseenter(ev); }),_xz=_xy(_xu,_xx);return _xx;},_xA=function(_xB,_xC,_){var _xD=E(_9M)(_xC),_xE=E(_9L)(_xD),_xF=_xr(_xB,_xE,_);return C > 19 ? new F(function(){return E(_9K)(E(_xF));}) : (++C,E(_9K)(E(_xF)));},_xG=function(_xH,_xI,_){var _xJ=__createJSFunc(2,function(_xK,_){var _xL=B(A2(E(_xH),_xK,_));return _2D;}),_xM=E(_xI),_xN=(function (ev, jq) { jq.mouseleave(ev); }),_xO=_xN(_xJ,_xM);return _xM;},_xP=function(_xQ,_xR,_){var _xS=E(_9M)(_xR),_xT=E(_9L)(_xS),_xU=_xG(_xQ,_xT,_);return C > 19 ? new F(function(){return E(_9K)(E(_xU));}) : (++C,E(_9K)(E(_xU)));},_xV=new T(function(){return unCStr("<span class=\'short-desc\'>");}),_xW=function(_xX,_xY,_){return C > 19 ? new F(function(){return _a5(_xX,E(_xY),_);}) : (++C,_a5(_xX,E(_xY),_));},_xZ=function(_y0,_y1,_){var _y2=E(_3C(_3F(_y0)).e);if(!_y2._){return _y1;}else{var _y3=_a1(_xV,E(_y1),_);return C > 19 ? new F(function(){return _xW(_y2.a,_y3,_);}) : (++C,_xW(_y2.a,_y3,_));}},_y4=new T(function(){return unCStr("<label>");}),_y5=new T(function(){return unCStr("<label class=\"link\" onclick=\"");}),_y6=new T(function(){return unCStr("\">");}),_y7=function(_y8,_y9,_){var _ya=_3C(_3F(_y8)),_yb=E(_ya.a);if(!_yb._){return _y9;}else{var _yc=_yb.a,_yd=E(_ya.g);if(!_yd._){var _ye=_a1(_y4,E(_y9),_);return C > 19 ? new F(function(){return _xW(_yc,_ye,_);}) : (++C,_xW(_yc,_ye,_));}else{var _yf=_a1(_R(_y5,new T(function(){return _R(_yd.a,_y6);},1)),E(_y9),_);return C > 19 ? new F(function(){return _xW(_yc,_yf,_);}) : (++C,_xW(_yc,_yf,_));}}},_yg=function(_yh,_){var _yi=_4b(unAppCStr("#",new T(function(){return _d7(_yh);})),_),_yj=_3h(_aG,_bc,E(_yi),_);return 0;},_yk=function(_yl,_ym,_){var _yn=(function (elJs, jq) { return jq.find(elJs); });return _yn(toJSStr(E(_yl)),_ym);},_yo=new T(function(){return unCStr("span");}),_yp=function(_yq,_){var _yr=_4b(unAppCStr("#",new T(function(){return _d7(_yq);})),_),_ys=E(_yr),_yt=_yk(_yo,_ys,_),_yu=E(_3C(_3F(_yq)).f);if(!_yu._){return 0;}else{var _yv=_cG(_yu.a,E(_yt),_),_yw=_3h(_aG,_aF,_ys,_);return 0;}},_yx=new T(function(){return unCStr("<td>");}),_yy=new T(function(){return unCStr("id");}),_yz=new T(function(){return unCStr("<table>");}),_yA=new T(function(){return unCStr("<tbody>");}),_yB=new T(function(){return unCStr("<tr>");}),_yC=new T(function(){return unCStr("<td class=\'labeltd\'>");}),_yD=new T(function(){return unCStr("more-space");}),_yE=function(_yF,_yG,_yH,_){var _yI=B(A1(_yF,_)),_yJ=_a1(_yz,E(_yH),_),_yK=B(_xA(function(_yL,_){return _yp(_yG,_);},E(_yJ),_)),_yM=B(_xP(function(_yN,_){return _yg(_yG,_);},E(_yK),_)),_yO=E(_9M),_yP=_yO(E(_yM)),_yQ=E(_9L),_yR=_yQ(_yP),_yS=_a1(_yA,_yR,_),_yT=_yO(E(_yS)),_yU=_yQ(_yT),_yV=_a1(_yB,_yU,_),_yW=_yO(E(_yV)),_yX=_yQ(_yW),_yY=_a1(_yC,_yX,_),_yZ=_yO(E(_yY)),_z0=_yQ(_yZ),_z1=_9B(_yD,_z0,_),_z2=B(_y7(_yG,_z1,_)),_z3=E(_9K),_z4=_z3(E(_z2)),_z5=_a1(_yx,_z4,_),_z6=_yO(E(_z5)),_z7=_yQ(_z6),_z8=E(_ac)(E(_yI),_z7),_z9=_z3(_z8),_za=_a1(_yx,_z9,_),_zb=B(_9N(_yy,new T(function(){return _un(_yG);},1),E(_za),_)),_zc=_z3(E(_zb)),_zd=_z3(_zc),_ze=_z3(_zd);return C > 19 ? new F(function(){return _xZ(_yG,_ze,_);}) : (++C,_xZ(_yG,_ze,_));},_zf=function(_zg,_zh,_){return _a1(_zg,E(_zh),_);},_zi=new T(function(){return unCStr("_optional_group");}),_zj=function(_zk){return _R(_3Y(_3C(_3F(_zk)).b),_zi);},_zl=function(_zm,_zn,_){var _zo=(function (s) { console.error(s); }),_zp=_zo(toJSStr(E(_zm)));return _zn;},_zq=new T(function(){return (function (jq) { return jq.prop('checked') === true; });}),_zr=new T(function(){return (function (jq) { return jq.length; });}),_zs=function(_zt,_){var _zu=(function (elId) { return $(elId); }),_zv=_zu(toJSStr(_R(_fo,new T(function(){return _R(_zt,_fn);},1)))),_zw=E(_zr)(_zv);return new T(function(){var _zx=Number(_zw),_zy=jsTrunc(_zx);return _zy>0;});},_zz=new T(function(){return unCStr(": empty list");}),_zA=function(_zB){return err(_R(_5R,new T(function(){return _R(_zB,_zz);},1)));},_zC=new T(function(){return _zA(new T(function(){return unCStr("last");}));}),_zD=new T(function(){return B(_tx("lfiAvailableOptions"));}),_zE=new T(function(){return unCStr("Submit");}),_zF=new T(function(){return unCStr("value");}),_zG=new T(function(){return unCStr("<input type=\'button\' class=\'submit\'>");}),_zH=new T(function(){return unCStr("<td class=\'labeltd more-space\' style=\'text-align: center\'>");}),_zI=new T(function(){return unCStr("<table style=\'margin-top: 10px\'>");}),_zJ=new T(function(){return unCStr("Save");}),_zK=new T(function(){return unCStr("<input type=\'submit\'>");}),_zL=new T(function(){return unCStr("MultipleGroupElement rendering not implemented yet");}),_zM=new T(function(){return unCStr("<div class=\'optional-section\'>");}),_zN=new T(function(){return unCStr("\u25be");}),_zO=new T(function(){return unCStr("#");}),_zP=new T(function(){return unCStr("checked");}),_zQ=new T(function(){return unCStr("name");}),_zR=new T(function(){return unCStr("<input type=\'checkbox\'>");}),_zS=new T(function(){return unCStr("level");}),_zT=new T(function(){return unCStr("<div class=\'optional-group\'>");}),_zU=new T(function(){return unCStr(">");}),_zV=new T(function(){return unCStr("<h");}),_zW=new T(function(){return unCStr("framed");}),_zX=new T(function(){return unCStr("<div class=\'simple-group\'>");}),_zY=new T(function(){return unCStr("selected");}),_zZ=new T(function(){return unCStr("<option>");}),_A0=new T(function(){return unCStr("identity");}),_A1=new T(function(){return unCStr("<select>");}),_A2=new T(function(){return unCStr("<div>");}),_A3=new T(function(){return unCStr("<br>");}),_A4=new T(function(){return unCStr("<input type=\'radio\'>");}),_A5=new T(function(){return unCStr("&nbsp;&nbsp;");}),_A6=new T(function(){return unCStr("&nbsp;");}),_A7=new T(function(){return unCStr("<input type=\'number\'>");}),_A8=new T(function(){return unCStr("<input type=\'email\'>");}),_A9=new T(function(){return unCStr("<textarea>");}),_Aa=new T(function(){return unCStr("<input type=\'text\'>");}),_Ab=new T(function(){return unCStr("renderElement did not unify");}),_Ac=new T(function(){return _3q(0,0,__Z);}),_Ad=function(_Ae){var _Af=E(_Ae);if(!_Af._){var _Ag=E(_Af.a);return (_Ag._==0)?E(_Ag.a):E(_Ag.b);}else{var _Ah=E(_Af.a);return (_Ah._==0)?E(_Ah.a):E(_Ah.b);}},_Ai=new T(function(){return unCStr("_detail");}),_Aj=function(_Ak,_Al){while(1){var _Am=(function(_An,_Ao){var _Ap=E(_Ao);if(!_Ap._){return __Z;}else{var _Aq=_Ap.a,_Ar=_Ap.b;if(!B(A1(_An,_Aq))){var _As=_An;_Ak=_As;_Al=_Ar;return __continue;}else{return new T2(1,_Aq,new T(function(){return _Aj(_An,_Ar);}));}}})(_Ak,_Al);if(_Am!=__continue){return _Am;}}},_At=function(_Au){var _Av=function(_Aw){var _Ax=function(_Ay){if(_Au<48){switch(E(_Au)){case 45:return true;case 95:return true;default:return false;}}else{if(_Au>57){switch(E(_Au)){case 45:return true;case 95:return true;default:return false;}}else{return true;}}};if(_Au<97){return _Ax(_);}else{if(_Au>122){return _Ax(_);}else{return true;}}};if(_Au<65){return _Av(_);}else{if(_Au>90){return _Av(_);}else{return true;}}},_Az=function(_AA){return _At(E(_AA));},_AB=new T(function(){return unCStr("_");}),_AC=function(_AD,_AE){var _AF=new T(function(){return _R(_AB,new T(function(){var _AG=E(_AE);if(!_AG._){var _AH=E(_AG.a);if(!_AH._){return _Aj(_Az,_AH.a);}else{return _Aj(_Az,_AH.b);}}else{var _AI=E(_AG.a);if(!_AI._){return _Aj(_Az,_AI.a);}else{return _Aj(_Az,_AI.b);}}},1));},1);return _R(_3Y(_3C(_3F(_AD)).b),_AF);},_AJ=new T(function(){return (function (js) {return $(js.target); });}),_AK=function(_AL,_AM,_AN,_AO,_){var _AP=function(_AQ,_){return C > 19 ? new F(function(){return _wo(_AL,_AM,_AN,_);}) : (++C,_wo(_AL,_AM,_AN,_));},_AR=E(_AL);switch(_AR._){case 0:return _zl(_Ab,_AO,_);case 1:var _AS=function(_){var _AT=_4b(_Aa,_),_AU=_3C(_AR.a),_AV=_9F(_zQ,_3Y(_AU.b),E(_AT),_),_AW=function(_,_AX){var _AY=_9F(_zF,_AR.b,_AX,_),_AZ=_xr(function(_B0,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_AY,_),_B1=_xc(function(_B2,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_AZ,_),_B3=_wC(function(_B4,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_B1,_);return _xG(function(_B5,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_B3,_);},_B6=E(_AU.c);if(!_B6._){var _B7=_9F(_A0,__Z,E(_AV),_);return _AW(_,E(_B7));}else{var _B8=_9F(_A0,_B6.a,E(_AV),_);return _AW(_,E(_B8));}};return C > 19 ? new F(function(){return _yE(_AS,_AR,_AO,_);}) : (++C,_yE(_AS,_AR,_AO,_));break;case 2:var _B9=function(_){var _Ba=_4b(_A9,_),_Bb=_3C(_AR.a),_Bc=_9F(_zQ,_3Y(_Bb.b),E(_Ba),_),_Bd=function(_,_Be){var _Bf=_9F(_zF,_AR.b,_Be,_),_Bg=_xr(function(_Bh,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_Bf,_),_Bi=_xc(function(_Bj,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_Bg,_),_Bk=_wC(function(_Bl,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_Bi,_);return _xG(function(_Bm,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_Bk,_);},_Bn=E(_Bb.c);if(!_Bn._){var _Bo=_9F(_A0,__Z,E(_Bc),_);return _Bd(_,E(_Bo));}else{var _Bp=_9F(_A0,_Bn.a,E(_Bc),_);return _Bd(_,E(_Bp));}};return C > 19 ? new F(function(){return _yE(_B9,_AR,_AO,_);}) : (++C,_yE(_B9,_AR,_AO,_));break;case 3:var _Bq=function(_){var _Br=_4b(_A8,_),_Bs=_3C(_AR.a),_Bt=_9F(_zQ,_3Y(_Bs.b),E(_Br),_),_Bu=function(_,_Bv){var _Bw=_9F(_zF,_AR.b,_Bv,_),_Bx=_xr(function(_By,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_Bw,_),_Bz=_xc(function(_BA,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_Bx,_),_BB=_wC(function(_BC,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_Bz,_);return _xG(function(_BD,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_BB,_);},_BE=E(_Bs.c);if(!_BE._){var _BF=_9F(_A0,__Z,E(_Bt),_);return _Bu(_,E(_BF));}else{var _BG=_9F(_A0,_BE.a,E(_Bt),_);return _Bu(_,E(_BG));}};return C > 19 ? new F(function(){return _yE(_Bq,_AR,_AO,_);}) : (++C,_yE(_Bq,_AR,_AO,_));break;case 4:var _BH=_AR.a,_BI=_a1(_yz,E(_AO),_),_BJ=B(_xA(function(_BK,_){return _yp(_AR,_);},E(_BI),_)),_BL=B(_xP(function(_BM,_){return _yg(_AR,_);},E(_BJ),_)),_BN=E(_9M),_BO=_BN(E(_BL)),_BP=E(_9L),_BQ=_BP(_BO),_BR=_a1(_yA,_BQ,_),_BS=_BN(E(_BR)),_BT=_BP(_BS),_BU=_a1(_yB,_BT,_),_BV=_BN(E(_BU)),_BW=_BP(_BV),_BX=_a1(_yC,_BW,_),_BY=_BN(E(_BX)),_BZ=_BP(_BY),_C0=_9B(_yD,_BZ,_),_C1=B(_y7(_AR,_C0,_)),_C2=E(_9K),_C3=_C2(E(_C1)),_C4=_a1(_yx,_C3,_),_C5=_BN(E(_C4)),_C6=_BP(_C5),_C7=_a1(_A7,_C6,_),_C8=B(_9N(_yy,new T(function(){return _3Y(_3C(_BH).b);},1),E(_C7),_)),_C9=B(_9N(_zQ,new T(function(){return _3Y(_3C(_BH).b);},1),E(_C8),_)),_Ca=B(_9N(_A0,new T(function(){var _Cb=E(_3C(_BH).c);if(!_Cb._){return __Z;}else{return E(_Cb.a);}},1),E(_C9),_)),_Cc=B(_9N(_zF,new T(function(){var _Cd=E(_AR.b);if(!_Cd._){return __Z;}else{return B(_3I(_Cd.a));}},1),E(_Ca),_)),_Ce=B(_xA(function(_Cf,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},E(_Cc),_)),_Cg=B(_xl(function(_Ch,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},E(_Ce),_)),_Ci=B(_x0(function(_Cj,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},E(_Cg),_)),_Ck=B(_wL(function(_Cl,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},E(_Ci),_)),_Cm=B(_xP(function(_Cn,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},E(_Ck),_)),_Co=_a1(_A6,E(_Cm),_),_Cp=E(_BH);if(_Cp._==3){var _Cq=function(_,_Cr){var _Cs=_C2(_Cr),_Ct=_a1(_yx,_Cs,_),_Cu=B(_9N(_yy,new T(function(){return _un(_AR);},1),E(_Ct),_)),_Cv=_C2(E(_Cu)),_Cw=_C2(_Cv),_Cx=_C2(_Cw);return C > 19 ? new F(function(){return _xZ(_AR,_Cx,_);}) : (++C,_xZ(_AR,_Cx,_));},_Cy=E(_Cp.b);switch(_Cy._){case 0:var _Cz=_a1(_Cy.a,E(_Co),_);return C > 19 ? new F(function(){return _Cq(_,E(_Cz));}) : (++C,_Cq(_,E(_Cz)));break;case 1:var _CA=new T(function(){return _R(_3Y(E(_Cp.a).b),_fw);}),_CB=function(_CC,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_CD=E(_Cy.a);if(!_CD._){return C > 19 ? new F(function(){return _Cq(_,E(_Co));}) : (++C,_Cq(_,E(_Co)));}else{var _CE=_CD.a,_CF=_CD.b,_CG=_a1(_A4,E(_Co),_),_CH=B(_9N(_zF,_CE,E(_CG),_)),_CI=B(_9N(_zQ,_CA,E(_CH),_)),_CJ=B(_xA(_AP,E(_CI),_)),_CK=B(_x6(_AP,E(_CJ),_)),_CL=B(_xP(_CB,E(_CK),_)),_CM=function(_,_CN){var _CO=_a1(_y4,_CN,_),_CP=B(_a5(_CE,E(_CO),_));return _zf(_A5,_CP,_);},_CQ=E(_AR.c);if(!_CQ._){var _CR=B(_CM(_,E(_CL))),_CS=function(_CT,_CU,_){while(1){var _CV=E(_CT);if(!_CV._){return _CU;}else{var _CW=_CV.a,_CX=_a1(_A4,E(_CU),_),_CY=B(_9N(_zF,_CW,E(_CX),_)),_CZ=B(_9N(_zQ,_CA,E(_CY),_)),_D0=B(_xA(_AP,E(_CZ),_)),_D1=B(_x6(_AP,E(_D0),_)),_D2=B(_xP(_CB,E(_D1),_)),_D3=_a1(_y4,E(_D2),_),_D4=B(_a5(_CW,E(_D3),_)),_D5=_a1(_A5,E(_D4),_);_CT=_CV.b;_CU=_D5;continue;}}},_D6=_CS(_CF,_CR,_);return C > 19 ? new F(function(){return _Cq(_,E(_D6));}) : (++C,_Cq(_,E(_D6)));}else{var _D7=_CQ.a;if(!_aH(_D7,_CE)){var _D8=B(_CM(_,E(_CL))),_D9=function(_Da,_Db,_){while(1){var _Dc=(function(_Dd,_De,_){var _Df=E(_Dd);if(!_Df._){return _De;}else{var _Dg=_Df.a,_Dh=_Df.b,_Di=_a1(_A4,E(_De),_),_Dj=B(_9N(_zF,_Dg,E(_Di),_)),_Dk=B(_9N(_zQ,_CA,E(_Dj),_)),_Dl=B(_xA(_AP,E(_Dk),_)),_Dm=B(_x6(_AP,E(_Dl),_)),_Dn=B(_xP(_CB,E(_Dm),_)),_Do=function(_,_Dp){var _Dq=_a1(_y4,_Dp,_),_Dr=B(_a5(_Dg,E(_Dq),_));return _zf(_A5,_Dr,_);};if(!_aH(_D7,_Dg)){var _Ds=B(_Do(_,E(_Dn)));_Da=_Dh;_Db=_Ds;return __continue;}else{var _Dt=B(_9N(_zP,_zP,E(_Dn),_)),_Du=B(_Do(_,E(_Dt)));_Da=_Dh;_Db=_Du;return __continue;}}})(_Da,_Db,_);if(_Dc!=__continue){return _Dc;}}},_Dv=_D9(_CF,_D8,_);return C > 19 ? new F(function(){return _Cq(_,E(_Dv));}) : (++C,_Cq(_,E(_Dv)));}else{var _Dw=B(_9N(_zP,_zP,E(_CL),_)),_Dx=B(_CM(_,E(_Dw))),_Dy=function(_Dz,_DA,_){while(1){var _DB=(function(_DC,_DD,_){var _DE=E(_DC);if(!_DE._){return _DD;}else{var _DF=_DE.a,_DG=_DE.b,_DH=_a1(_A4,E(_DD),_),_DI=B(_9N(_zF,_DF,E(_DH),_)),_DJ=B(_9N(_zQ,_CA,E(_DI),_)),_DK=B(_xA(_AP,E(_DJ),_)),_DL=B(_x6(_AP,E(_DK),_)),_DM=B(_xP(_CB,E(_DL),_)),_DN=function(_,_DO){var _DP=_a1(_y4,_DO,_),_DQ=B(_a5(_DF,E(_DP),_));return _zf(_A5,_DQ,_);};if(!_aH(_D7,_DF)){var _DR=B(_DN(_,E(_DM)));_Dz=_DG;_DA=_DR;return __continue;}else{var _DS=B(_9N(_zP,_zP,E(_DM),_)),_DT=B(_DN(_,E(_DS)));_Dz=_DG;_DA=_DT;return __continue;}}})(_Dz,_DA,_);if(_DB!=__continue){return _DB;}}},_DU=_Dy(_CF,_Dx,_);return C > 19 ? new F(function(){return _Cq(_,E(_DU));}) : (++C,_Cq(_,E(_DU)));}}}break;default:return C > 19 ? new F(function(){return _Cq(_,E(_Co));}) : (++C,_Cq(_,E(_Co)));}}else{return E(_vI);}break;case 5:var _DV=_AR.a,_DW=_AR.b,_DX=new T(function(){return _3Y(_3C(_DV).b);}),_DY=_a1(_yz,E(_AO),_),_DZ=B(_xA(function(_E0,_){return _yp(_AR,_);},E(_DY),_)),_E1=B(_xP(function(_E2,_){return _yg(_AR,_);},E(_DZ),_)),_E3=E(_9M),_E4=_E3(E(_E1)),_E5=E(_9L),_E6=_E5(_E4),_E7=_a1(_yA,_E6,_),_E8=_E3(E(_E7)),_E9=_E5(_E8),_Ea=_a1(_yB,_E9,_),_Eb=_E3(E(_Ea)),_Ec=_E5(_Eb),_Ed=_a1(_yC,_Ec,_),_Ee=_E3(E(_Ed)),_Ef=_E5(_Ee),_Eg=_9B(_yD,_Ef,_),_Eh=B(_y7(_AR,_Eg,_)),_Ei=E(_9K),_Ej=_Ei(E(_Eh)),_Ek=_a1(_yx,_Ej,_),_El=_E3(E(_Ek)),_Em=_E5(_El),_En=new T(function(){var _Eo=E(_3C(_DV).c);if(!_Eo._){return __Z;}else{return E(_Eo.a);}}),_Ep=function(_Eq,_){var _Er=_zs(_DX,_);return _uw(_AR,_AM,_Er,_);},_Es=new T(function(){var _Et=function(_Eu,_Ev){while(1){var _Ew=E(_Eu);if(!_Ew._){return E(_Ev);}else{_Eu=_Ew.b;_Ev=_Ew.a;continue;}}};return _Et(_DW,_zC);}),_Ex=function(_Ey,_){return _4b(_R(_zO,new T(function(){return _R(_AC(_AR,_Ey),_Ai);},1)),_);},_Ez=function(_EA,_){while(1){var _EB=E(_EA);if(!_EB._){return __Z;}else{var _EC=_EB.b,_ED=E(_EB.a);if(!_ED._){_EA=_EC;continue;}else{var _EE=_Ex(_ED,_),_EF=_Ez(_EC,_);return new T2(1,_EE,_EF);}}}},_EG=function(_EH,_EI,_){while(1){var _EJ=(function(_EK,_EL,_){var _EM=E(_EK);if(!_EM._){return _EL;}else{var _EN=_EM.a,_EO=_EM.b,_EP=_a1(_A4,E(_EL),_),_EQ=B(_9N(_yy,new T(function(){return _AC(_AR,_EN);},1),E(_EP),_)),_ER=B(_9N(_zQ,_DX,E(_EQ),_)),_ES=B(_9N(_A0,_En,E(_ER),_)),_ET=B(_9N(_zF,new T(function(){return _Ad(_EN);},1),E(_ES),_)),_EU=function(_,_EV){var _EW=function(_EX,_){var _EY=_Ez(_DW,_),_EZ=function(_F0,_){while(1){var _F1=E(_F0);if(!_F1._){return 0;}else{var _F2=_3h(_aG,_bc,E(_F1.a),_);_F0=_F1.b;continue;}}},_F3=_EZ(_EY,_),_F4=E(_EN);if(!_F4._){var _F5=_zs(_DX,_);return _uw(_AR,_AM,_F5,_);}else{var _F6=_Ex(_F4,_),_F7=_3h(_aG,_aF,E(_F6),_),_F8=_zs(_DX,_);return _uw(_AR,_AM,_F8,_);}},_F9=B(_x6(_EW,_EV,_)),_Fa=B(_xP(_Ep,E(_F9),_)),_Fb=_a1(_y4,E(_Fa),_),_Fc=B(_a5(new T(function(){return _Ad(_EN);},1),E(_Fb),_)),_Fd=E(_EN);if(!_Fd._){var _Fe=_Fd.a,_Ff=_a1(__Z,E(_Fc),_),_Fg=E(_Es);if(!_Fg._){if(!_dc(_Fe,_Fg.a)){return _zf(_A3,_Ff,_);}else{return _Ff;}}else{if(!_dc(_Fe,_Fg.a)){return _zf(_A3,_Ff,_);}else{return _Ff;}}}else{var _Fh=_Fd.a,_Fi=_a1(_zN,E(_Fc),_),_Fj=E(_Es);if(!_Fj._){if(!_dc(_Fh,_Fj.a)){return _zf(_A3,_Fi,_);}else{return _Fi;}}else{if(!_dc(_Fh,_Fj.a)){return _zf(_A3,_Fi,_);}else{return _Fi;}}}},_Fk=E(_EN);if(!_Fk._){if(!E(_Fk.b)){var _Fl=B(_EU(_,E(_ET)));_EH=_EO;_EI=_Fl;return __continue;}else{var _Fm=B(_9N(_zP,_zP,E(_ET),_)),_Fn=B(_EU(_,E(_Fm)));_EH=_EO;_EI=_Fn;return __continue;}}else{if(!E(_Fk.b)){var _Fo=B(_EU(_,E(_ET)));_EH=_EO;_EI=_Fo;return __continue;}else{var _Fp=B(_9N(_zP,_zP,E(_ET),_)),_Fq=B(_EU(_,E(_Fp)));_EH=_EO;_EI=_Fq;return __continue;}}}})(_EH,_EI,_);if(_EJ!=__continue){return _EJ;}}},_Fr=function(_Fs,_Ft,_Fu,_){var _Fv=E(_Fs);if(!_Fv._){return _Ft;}else{var _Fw=_Fv.a,_Fx=_Fv.b,_Fy=_a1(_A4,_Ft,_),_Fz=B(_9N(_yy,new T(function(){return _AC(_AR,_Fw);},1),E(_Fy),_)),_FA=B(_9N(_zQ,_DX,E(_Fz),_)),_FB=B(_9N(_A0,_En,E(_FA),_)),_FC=B(_9N(_zF,new T(function(){return _Ad(_Fw);},1),E(_FB),_)),_FD=function(_,_FE){var _FF=function(_FG,_){var _FH=_Ez(_DW,_),_FI=function(_FJ,_){while(1){var _FK=E(_FJ);if(!_FK._){return 0;}else{var _FL=_3h(_aG,_bc,E(_FK.a),_);_FJ=_FK.b;continue;}}},_FM=_FI(_FH,_),_FN=E(_Fw);if(!_FN._){var _FO=_zs(_DX,_);return _uw(_AR,_AM,_FO,_);}else{var _FP=_Ex(_FN,_),_FQ=_3h(_aG,_aF,E(_FP),_),_FR=_zs(_DX,_);return _uw(_AR,_AM,_FR,_);}},_FS=B(_x6(_FF,_FE,_)),_FT=B(_xP(_Ep,E(_FS),_)),_FU=_a1(_y4,E(_FT),_),_FV=B(_a5(new T(function(){return _Ad(_Fw);},1),E(_FU),_)),_FW=E(_Fw);if(!_FW._){var _FX=_FW.a,_FY=_a1(__Z,E(_FV),_),_FZ=E(_Es);if(!_FZ._){if(!_dc(_FX,_FZ.a)){return _zf(_A3,_FY,_);}else{return _FY;}}else{if(!_dc(_FX,_FZ.a)){return _zf(_A3,_FY,_);}else{return _FY;}}}else{var _G0=_FW.a,_G1=_a1(_zN,E(_FV),_),_G2=E(_Es);if(!_G2._){if(!_dc(_G0,_G2.a)){return _zf(_A3,_G1,_);}else{return _G1;}}else{if(!_dc(_G0,_G2.a)){return _zf(_A3,_G1,_);}else{return _G1;}}}},_G3=E(_Fw);if(!_G3._){if(!E(_G3.b)){var _G4=B(_FD(_,E(_FC)));return _EG(_Fx,_G4,_);}else{var _G5=B(_9N(_zP,_zP,E(_FC),_)),_G6=B(_FD(_,E(_G5)));return _EG(_Fx,_G6,_);}}else{if(!E(_G3.b)){var _G7=B(_FD(_,E(_FC)));return _EG(_Fx,_G7,_);}else{var _G8=B(_9N(_zP,_zP,E(_FC),_)),_G9=B(_FD(_,E(_G8)));return _EG(_Fx,_G9,_);}}}},_Ga=_Fr(_DW,_Em,_,_),_Gb=_Ei(E(_Ga)),_Gc=_a1(_yx,_Gb,_),_Gd=B(_9N(_yy,new T(function(){return _un(_AR);},1),E(_Gc),_)),_Ge=_Ei(E(_Gd)),_Gf=_Ei(_Ge),_Gg=_Ei(_Gf),_Gh=function(_,_Gi){var _Gj=function(_Gk,_Gl,_){while(1){var _Gm=E(_Gk);if(!_Gm._){return _Gl;}else{var _Gn=B(_AK(_Gm.a,_AM,_AN,_Gl,_));_Gk=_Gm.b;_Gl=_Gn;continue;}}},_Go=function(_Gp,_Gq,_Gr,_){while(1){var _Gs=(function(_Gt,_Gu,_Gv,_){var _Gw=E(_Gt);if(!_Gw._){return _Gu;}else{var _Gx=_Gw.b,_Gy=E(_Gw.a);if(!_Gy._){var _Gz=_Gu,_GA=_;_Gp=_Gx;_Gq=_Gz;_Gr=_GA;return __continue;}else{var _GB=_a1(_A2,_Gu,_),_GC=B(_9N(_yy,new T(function(){return _R(_AC(_AR,_Gy),_Ai);},1),E(_GB),_)),_GD=_E3(E(_GC)),_GE=_E5(_GD),_GF=_3h(_aG,_bc,_GE,_),_GG=_Gj(_Gy.c,_GF,_),_GH=_Ei(E(_GG)),_GA=_;_Gp=_Gx;_Gq=_GH;_Gr=_GA;return __continue;}}})(_Gp,_Gq,_Gr,_);if(_Gs!=__continue){return _Gs;}}},_GI=function(_GJ,_GK,_){while(1){var _GL=(function(_GM,_GN,_){var _GO=E(_GM);if(!_GO._){return _GN;}else{var _GP=_GO.b,_GQ=E(_GO.a);if(!_GQ._){var _GR=_GN;_GJ=_GP;_GK=_GR;return __continue;}else{var _GS=_a1(_A2,E(_GN),_),_GT=B(_9N(_yy,new T(function(){return _R(_AC(_AR,_GQ),_Ai);},1),E(_GS),_)),_GU=_E3(E(_GT)),_GV=_E5(_GU),_GW=_3h(_aG,_bc,_GV,_),_GX=_Gj(_GQ.c,_GW,_),_GY=_Ei(E(_GX));return _Go(_GP,_GY,_,_);}}})(_GJ,_GK,_);if(_GL!=__continue){return _GL;}}};return _GI(_DW,_Gi,_);},_GZ=E(_3C(_DV).e);if(!_GZ._){return _Gh(_,_Gg);}else{var _H0=_a1(_xV,_Gg,_),_H1=B(_a5(_GZ.a,E(_H0),_));return _Gh(_,_H1);}break;case 6:var _H2=_AR.a,_H3=function(_){var _H4=_4b(_A1,_),_H5=_3C(_H2),_H6=_9F(_zQ,_3Y(_H5.b),E(_H4),_),_H7=function(_,_H8){var _H9=_wC(function(_Ha,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_H8,_),_Hb=_wR(function(_Hc,_){return C > 19 ? new F(function(){return _wo(_AR,_AM,_AN,_);}) : (++C,_wo(_AR,_AM,_AN,_));},_H9,_),_Hd=_xG(function(_He,_){return C > 19 ? new F(function(){return _wh(_AR,_AM,_AN,_);}) : (++C,_wh(_AR,_AM,_AN,_));},_Hb,_),_Hf=E(_H2);if(_Hf._==5){var _Hg=E(_Hf.b);if(!_Hg._){return _Hd;}else{var _Hh=_Hg.b,_Hi=E(_Hg.a),_Hj=_Hi.a,_Hk=_a1(_zZ,E(_Hd),_),_Hl=B(_9N(_zF,_Hj,E(_Hk),_)),_Hm=B(_a5(_Hi.b,E(_Hl),_)),_Hn=E(_AR.b);if(!_Hn._){var _Ho=function(_Hp,_Hq,_){while(1){var _Hr=E(_Hp);if(!_Hr._){return _Hq;}else{var _Hs=E(_Hr.a),_Ht=_a1(_zZ,E(_Hq),_),_Hu=B(_9N(_zF,_Hs.a,E(_Ht),_)),_Hv=B(_a5(_Hs.b,E(_Hu),_));_Hp=_Hr.b;_Hq=_Hv;continue;}}};return _Ho(_Hh,_Hm,_);}else{var _Hw=_Hn.a;if(!_aH(_Hj,_Hw)){var _Hx=function(_Hy,_Hz,_){while(1){var _HA=E(_Hy);if(!_HA._){return _Hz;}else{var _HB=_HA.b,_HC=E(_HA.a),_HD=_HC.a,_HE=_a1(_zZ,E(_Hz),_),_HF=B(_9N(_zF,_HD,E(_HE),_)),_HG=B(_a5(_HC.b,E(_HF),_));if(!_aH(_HD,_Hw)){_Hy=_HB;_Hz=_HG;continue;}else{var _HH=B(_9N(_zY,_zY,E(_HG),_));_Hy=_HB;_Hz=_HH;continue;}}}};return _Hx(_Hh,_Hm,_);}else{var _HI=B(_9N(_zY,_zY,E(_Hm),_)),_HJ=function(_HK,_HL,_){while(1){var _HM=E(_HK);if(!_HM._){return _HL;}else{var _HN=_HM.b,_HO=E(_HM.a),_HP=_HO.a,_HQ=_a1(_zZ,E(_HL),_),_HR=B(_9N(_zF,_HP,E(_HQ),_)),_HS=B(_a5(_HO.b,E(_HR),_));if(!_aH(_HP,_Hw)){_HK=_HN;_HL=_HS;continue;}else{var _HT=B(_9N(_zY,_zY,E(_HS),_));_HK=_HN;_HL=_HT;continue;}}}};return _HJ(_Hh,_HI,_);}}}}else{return E(_zD);}},_HU=E(_H5.c);if(!_HU._){var _HV=_9F(_A0,__Z,E(_H6),_);return _H7(_,_HV);}else{var _HW=_9F(_A0,_HU.a,E(_H6),_);return _H7(_,_HW);}};return C > 19 ? new F(function(){return _yE(_H3,_AR,_AO,_);}) : (++C,_yE(_H3,_AR,_AO,_));break;case 7:var _HX=_AR.a,_HY=_AR.b,_HZ=_a1(_zX,E(_AO),_),_I0=new T(function(){var _I1=E(_HX);switch(_I1._){case 7:return E(_I1.b);break;case 8:return E(_I1.b);break;case 9:return E(_I1.b);break;default:return 0;}}),_I2=B(_9N(_zS,new T(function(){return B(_3I(_I0));},1),E(_HZ),_)),_I3=E(_I0),_I4=function(_,_I5){var _I6=E(_9M)(_I5),_I7=E(_9L)(_I6),_I8=_3C(_HX),_I9=_I8.e,_Ia=E(_I8.a);if(!_Ia._){var _Ib=function(_,_Ic){var _Id=function(_Ie,_If,_){while(1){var _Ig=E(_Ie);if(!_Ig._){return _If;}else{var _Ih=B(_AK(_Ig.a,_AM,_AN,_If,_));_Ie=_Ig.b;_If=_Ih;continue;}}},_Ii=_Id(_HY,_Ic,_);return C > 19 ? new F(function(){return E(_9K)(E(_Ii));}) : (++C,E(_9K)(E(_Ii)));},_Ij=E(_I9);if(!_Ij._){return C > 19 ? new F(function(){return _Ib(_,_I7);}) : (++C,_Ib(_,_I7));}else{var _Ik=_a1(_xV,_I7,_),_Il=B(_a5(_Ij.a,E(_Ik),_));return C > 19 ? new F(function(){return _Ib(_,_Il);}) : (++C,_Ib(_,_Il));}}else{var _Im=_a1(_R(_zV,new T(function(){return _R(_3q(0,_I3,__Z),_zU);},1)),_I7,_),_In=B(_a5(_Ia.a,E(_Im),_)),_Io=function(_,_Ip){var _Iq=function(_Ir,_Is,_){while(1){var _It=E(_Ir);if(!_It._){return _Is;}else{var _Iu=B(_AK(_It.a,_AM,_AN,_Is,_));_Ir=_It.b;_Is=_Iu;continue;}}},_Iv=_Iq(_HY,_Ip,_);return C > 19 ? new F(function(){return E(_9K)(E(_Iv));}) : (++C,E(_9K)(E(_Iv)));},_Iw=E(_I9);if(!_Iw._){return C > 19 ? new F(function(){return _Io(_,_In);}) : (++C,_Io(_,_In));}else{var _Ix=_a1(_xV,E(_In),_),_Iy=B(_a5(_Iw.a,E(_Ix),_));return C > 19 ? new F(function(){return _Io(_,_Iy);}) : (++C,_Io(_,_Iy));}}};if(_I3<=1){return C > 19 ? new F(function(){return _I4(_,E(_I2));}) : (++C,_I4(_,E(_I2)));}else{var _Iz=B(_wv(_zW,E(_I2),_));return C > 19 ? new F(function(){return _I4(_,E(_Iz));}) : (++C,_I4(_,E(_Iz)));}break;case 8:var _IA=_AR.a,_IB=_AR.c,_IC=_a1(_zT,E(_AO),_),_ID=B(_9N(_zS,new T(function(){var _IE=E(_IA);switch(_IE._){case 7:return _3q(0,E(_IE.b),__Z);break;case 8:return _3q(0,E(_IE.b),__Z);break;case 9:return _3q(0,E(_IE.b),__Z);break;default:return E(_Ac);}},1),E(_IC),_)),_IF=B(_xA(function(_IG,_){return _yp(_AR,_);},E(_ID),_)),_IH=B(_xP(function(_II,_){return _yg(_AR,_);},E(_IF),_)),_IJ=E(_9M),_IK=_IJ(E(_IH)),_IL=E(_9L),_IM=_IL(_IK),_IN=_a1(_zR,_IM,_),_IO=B(_9N(_zQ,new T(function(){return _3Y(_3C(_IA).b);},1),E(_IN),_)),_IP=function(_,_IQ){var _IR=new T(function(){return _R(_zO,new T(function(){return _zj(_AR);},1));}),_IS=B(_x6(function(_IT,_){var _IU=_4b(_IR,_),_IV=E(_AJ)(E(_IT)),_IW=E(_zq)(_IV);if(!_IW){var _IX=_3h(_aG,_bc,E(_IU),_);return 0;}else{var _IY=_3h(_aG,_aF,E(_IU),_);return 0;}},_IQ,_)),_IZ=B(_y7(_AR,_IS,_)),_J0=function(_,_J1){var _J2=function(_,_J3){var _J4=E(_IB);if(!_J4._){return C > 19 ? new F(function(){return E(_9K)(_J3);}) : (++C,E(_9K)(_J3));}else{var _J5=_a1(_zM,_J3,_),_J6=B(_9N(_yy,new T(function(){return _zj(_AR);},1),E(_J5),_)),_J7=_IJ(E(_J6)),_J8=_IL(_J7),_J9=function(_Ja,_Jb,_){while(1){var _Jc=E(_Ja);if(!_Jc._){return _Jb;}else{var _Jd=B(_AK(_Jc.a,_AM,_AN,_Jb,_));_Ja=_Jc.b;_Jb=_Jd;continue;}}},_Je=(function(_Jf,_Jg,_Jh,_){var _Ji=B(_AK(_Jf,_AM,_AN,_Jh,_));return _J9(_Jg,_Ji,_);})(_J4.a,_J4.b,_J8,_),_Jj=E(_9K),_Jk=_Jj(E(_Je));return C > 19 ? new F(function(){return _Jj(_Jk);}) : (++C,_Jj(_Jk));}},_Jl=E(_3C(_IA).e);if(!_Jl._){return C > 19 ? new F(function(){return _J2(_,_J1);}) : (++C,_J2(_,_J1));}else{var _Jm=_a1(_xV,_J1,_),_Jn=B(_a5(_Jl.a,E(_Jm),_));return C > 19 ? new F(function(){return _J2(_,E(_Jn));}) : (++C,_J2(_,E(_Jn)));}};if(!E(_IB)._){var _Jo=_a1(__Z,E(_IZ),_);return C > 19 ? new F(function(){return _J0(_,E(_Jo));}) : (++C,_J0(_,E(_Jo)));}else{var _Jp=_a1(_zN,E(_IZ),_);return C > 19 ? new F(function(){return _J0(_,E(_Jp));}) : (++C,_J0(_,E(_Jp)));}};if(!E(_AR.b)){return C > 19 ? new F(function(){return _IP(_,E(_IO));}) : (++C,_IP(_,E(_IO)));}else{var _Jq=B(_9N(_zP,_zP,E(_IO),_));return C > 19 ? new F(function(){return _IP(_,E(_Jq));}) : (++C,_IP(_,E(_Jq)));}break;case 9:return _zl(_zL,_AO,_);case 10:var _Jr=_a1(_zI,E(_AO),_),_Js=E(_9M),_Jt=_Js(E(_Jr)),_Ju=E(_9L),_Jv=_Ju(_Jt),_Jw=_a1(_yA,_Jv,_),_Jx=_Js(E(_Jw)),_Jy=_Ju(_Jx),_Jz=_a1(_yB,_Jy,_),_JA=_Js(E(_Jz)),_JB=_Ju(_JA),_JC=_a1(_zH,_JB,_),_JD=_Js(E(_JC)),_JE=_Ju(_JD),_JF=_a1(_zK,_JE,_),_JG=B(_9N(_zF,new T(function(){var _JH=E(_3C(_AR.a).a);if(!_JH._){return E(_zJ);}else{return E(_JH.a);}},1),E(_JF),_)),_JI=E(_9K),_JJ=_JI(E(_JG)),_JK=_JI(_JJ),_JL=_JI(_JK),_JM=_JI(_JL);return C > 19 ? new F(function(){return _xZ(_AR,_JM,_);}) : (++C,_xZ(_AR,_JM,_));break;default:var _JN=_a1(_zI,E(_AO),_),_JO=E(_9M),_JP=_JO(E(_JN)),_JQ=E(_9L),_JR=_JQ(_JP),_JS=_a1(_yA,_JR,_),_JT=_JO(E(_JS)),_JU=_JQ(_JT),_JV=_a1(_yB,_JU,_),_JW=_JO(E(_JV)),_JX=_JQ(_JW),_JY=_a1(_zH,_JX,_),_JZ=_JO(E(_JY)),_K0=_JQ(_JZ),_K1=_a1(_zG,_K0,_),_K2=B(_9N(_zF,new T(function(){var _K3=E(_3C(_AR.a).a);if(!_K3._){return E(_zE);}else{return E(_K3.a);}},1),E(_K1),_)),_K4=E(_9K),_K5=_K4(E(_K2)),_K6=_K4(_K5),_K7=_K4(_K6),_K8=_K4(_K7);return C > 19 ? new F(function(){return _xZ(_AR,_K8,_);}) : (++C,_xZ(_AR,_K8,_));}},_K9=function(_Ka,_Kb,_Kc,_Kd,_){var _Ke=function(_Kf,_Kg,_){while(1){var _Kh=E(_Kf);if(!_Kh._){return _Kg;}else{var _Ki=B(_AK(_Kh.a,_Kb,_Kc,_Kg,_));_Kf=_Kh.b;_Kg=_Ki;continue;}}};return _Ke(_Ka,_Kd,_);},_Kj=new T(function(){return unCStr("textarea");}),_Kk=new T(function(){return unCStr("select");}),_Kl=function(_Km,_Kn,_){var _Ko=(function (selector, jq) { if (jq[0].contentDocument !== null) { var res = $(selector, jq[0].contentDocument.documentElement); if (res.length === 0) { console.warn('empty $ selection ' + selector); }; return res; } else return jq; });return _Ko(toJSStr(E(_Km)),_Kn);},_Kp=new T(function(){return unCStr("#FBB48F");}),_Kq=new T(function(){return unCStr("fill");}),_Kr=new T(function(){return unCStr("#");}),_Ks=function(_Kt,_Ku,_){var _Kv=_4b(_R(_Kr,_Ku),_),_Kw=_Kl(_R(_Kr,_Kt),E(_Kv),_),_Kx=_3h(_Kq,_Kp,E(_Kw),_);return 0;},_Ky=function(_Kz,_){var _KA=new T(function(){return _da(_Kz);}),_KB=function(_KC,_){while(1){var _KD=E(_KC);if(!_KD._){return 0;}else{var _KE=_Ks(_KD.a,_KA,_);_KC=_KD.b;continue;}}},_KF=_KB(_3C(_3F(_Kz)).d,_);return 0;},_KG=function(_KH,_KI,_){return _Ky(_KH,_);},_KJ=new T(function(){return unCStr("white");}),_KK=function(_KL,_){var _KM=new T(function(){return _R(_Kr,new T(function(){return _da(_KL);},1));}),_KN=function(_KO,_){while(1){var _KP=E(_KO);if(!_KP._){return 0;}else{var _KQ=_4b(_KM,_),_KR=_Kl(_R(_Kr,_KP.a),E(_KQ),_),_KS=_3h(_Kq,_KJ,E(_KR),_);_KO=_KP.b;continue;}}},_KT=_KN(_3C(_3F(_KL)).d,_);return 0;},_KU=function(_KV,_KW,_){return _KK(_KV,_);},_KX=new T(function(){return unCStr("<div class=\'desc-subpane\'>");}),_KY=new T(function(){return unCStr("id");}),_KZ=new T(function(){return unCStr("<object class=\'svg-help\' href=\'http://caniuse.com/#feat=svg\' data=\'/static/img/data_process.svg\' type=\'image/svg+xml\'><br>");}),_L0=new T(function(){return unCStr("<p class=\'long-desc\'>");}),_L1=new T(function(){return _R(new T(function(){return unCStr("/");}),new T(function(){return unCStr("static/");}));}),_L2=new T(function(){return unAppCStr("<img src=\'",new T(function(){return _R(_L1,new T(function(){return unCStr("/img/hint-icon.png\' style=\'margin-right: 5px;\'>");}));}));}),_L3=new T(function(){return unCStr("<span/>");}),_L4=new T(function(){return unCStr("#m_questionnaire_form");}),_L5=new T(function(){return unCStr("<div class=\'main-pane\'></div>");}),_L6=new T(function(){return unCStr("input");}),_L7=new T(function(){return unCStr("input:checked");}),_L8=new T(function(){return unCStr("<div class=\'form-subpane\'>");}),_L9=new T(function(){return unAppCStr("<img class=\'validity-flag\' src=\'",new T(function(){return _R(_L1,new T(function(){return unCStr("/img/valid.png\'/>");}));}));}),_La=new T(function(){return unAppCStr("<img class=\'validity-flag\' src=\'",new T(function(){return _R(_L1,new T(function(){return unCStr("/img/invalid.png\'/>");}));}));}),_Lb=function(_Lc,_){return _cZ(E(_Lc),_);},_Ld=function(_Le,_Lf,_){var _Lg=new T(function(){return _aA(new T(function(){return _5Z(_Lf,E(_Le));},1));},1),_Lh=_4b(_R(_aV,_Lg),_);return _Lb(_Lh,_);},_Li=new T(function(){return unCStr("box_3");}),_Lj=new T(function(){return unCStr("box_6");}),_Lk=new T(function(){return unCStr("box_5_e");}),_Ll=new T(function(){return unCStr("box_5_i");}),_Lm=new T(function(){return unCStr("box_4_1");}),_Ln=new T(function(){return unCStr("box_2");}),_Lo=new T(function(){return unCStr("institution_box");}),_Lp=new T(function(){return unCStr("box_1");}),_Lq=function(_Lr,_){var _Ls=_3Y(_3C(_3F(_Lr)).b);if(!_Ls._){return 0;}else{var _Lt=_Ls.b;switch(E(_Ls.a)){case 48:if(!E(_Lt)._){var _Lu=_Ks(_Lo,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 49:if(!E(_Lt)._){var _Lv=_Ks(_Lp,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 50:if(!E(_Lt)._){var _Lw=_Ks(_Ln,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 51:if(!E(_Lt)._){var _Lx=_Ks(_Li,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 52:if(!E(_Lt)._){var _Ly=_Ks(_Lm,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 53:if(!E(_Lt)._){var _Lz=new T(function(){return _da(_Lr);}),_LA=_Ks(_Ll,_Lz,_),_LB=_Ks(_Lk,_Lz,_);return 0;}else{return 0;}break;case 54:if(!E(_Lt)._){var _LC=_Ks(_Lj,new T(function(){return _da(_Lr);},1),_);return 0;}else{return 0;}break;case 55:var _LD=E(_Lt);return 0;default:return 0;}}},_LE=function(_LF,_){var _LG=_4b(_L4,_),_LH=new T2(1,new T3(0,new T2(6,{_:0,a:new T1(1,_d3),b:new T2(1,new T2(1,1000,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_LF),_LI=new T(function(){var _LJ=function(_LK,_){var _LL=_4b(_L5,_),_LM=_a1(_L8,E(_LL),_),_LN=E(_9M),_LO=_LN(E(_LM)),_LP=E(_9L),_LQ=_LP(_LO),_LR=_K9(_9y(_LK),new T3(0,_LF,_L9,_La),new T2(0,_KG,_KU),_LQ,_),_LS=E(_9K),_LT=_LS(E(_LR)),_LU=_a1(_KX,_LT,_),_LV=B(_9N(_KY,new T(function(){return _43(_LK);},1),E(_LU),_)),_LW=_LN(E(_LV)),_LX=_LP(_LW),_LY=_cG(_KZ,_LX,_),_LZ=B(_9N(_KY,new T(function(){return _da(_LK);},1),E(_LY),_)),_M0=B(_cT(function(_M1,_){return _Lq(_LK,_);},E(_LZ),_)),_M2=_a1(_L0,E(_M0),_),_M3=B(_9N(_KY,new T(function(){return _d7(_LK);},1),E(_M2),_)),_M4=_LN(E(_M3)),_M5=_LP(_M4),_M6=_a1(_L2,_M5,_),_M7=_a1(_L3,E(_M6),_),_M8=_LS(E(_M7));return C > 19 ? new F(function(){return _LS(_M8);}) : (++C,_LS(_M8));};return _2m(_LJ,_LF);}),_M9=_bu(_LH,new T2(1,_d5,_LI),E(_LG),_),_Ma=_Ld(0,_LH,_),_Mb=_4b(_L7,_),_Mc=_cZ(E(_Mb),_),_Md=_cZ(E(_Mc),_),_Me=_4b(_L6,_),_Mf=_cC(E(_Me),_),_Mg=_4b(_Kj,_),_Mh=_cC(E(_Mg),_),_Mi=_4b(_Kk,_),_Mj=_cC(E(_Mi),_);return 0;},_Mk=function(_Ml){while(1){var _Mm=E(_Ml);if(!_Mm._){return false;}else{if(!E(_Mm.a)._){return true;}else{_Ml=_Mm.b;continue;}}}},_Mn=new T(function(){return unCStr("Generate");}),_Mo=new T(function(){return unCStr("Error generating tabs");}),_Mp=function(_Mq,_Mr){return C > 19 ? new F(function(){return _Ms(_Mr);}) : (++C,_Ms(_Mr));},_Ms=function(_Mt){var _Mu=new T(function(){return B(_qq(function(_Mv){var _Mw=E(_Mv);if(!_Mw._){return C > 19 ? new F(function(){return A1(_Mt,_Mw.a);}) : (++C,A1(_Mt,_Mw.a));}else{return new T0(2);}}));}),_Mx=function(_My){return E(_Mu);};return _gF(new T1(1,function(_Mz){return C > 19 ? new F(function(){return A2(_pj,_Mz,_Mx);}) : (++C,A2(_pj,_Mz,_Mx));}),new T(function(){return new T1(1,_qX(_Mp,_Mt));}));},_MA=function(_MB,_MC){return C > 19 ? new F(function(){return _Ms(_MC);}) : (++C,_Ms(_MC));},_MD=new T(function(){return unCStr("[");}),_ME=function(_MF,_MG){var _MH=function(_MI,_MJ){var _MK=new T(function(){return B(A1(_MJ,__Z));}),_ML=new T(function(){var _MM=function(_MN){return _MH(true,function(_MO){return C > 19 ? new F(function(){return A1(_MJ,new T2(1,_MN,_MO));}) : (++C,A1(_MJ,new T2(1,_MN,_MO)));});};return B(A2(_MF,0,_MM));}),_MP=new T(function(){return B(_qq(function(_MQ){var _MR=E(_MQ);if(_MR._==2){var _MS=E(_MR.a);if(!_MS._){return new T0(2);}else{var _MT=_MS.b;switch(E(_MS.a)){case 44:return (E(_MT)._==0)?(!E(_MI))?new T0(2):E(_ML):new T0(2);case 93:return (E(_MT)._==0)?E(_MK):new T0(2);default:return new T0(2);}}}else{return new T0(2);}}));}),_MU=function(_MV){return E(_MP);};return new T1(1,function(_MW){return C > 19 ? new F(function(){return A2(_pj,_MW,_MU);}) : (++C,A2(_pj,_MW,_MU));});},_MX=function(_MY,_MZ){return C > 19 ? new F(function(){return _N0(_MZ);}) : (++C,_N0(_MZ));},_N0=function(_N1){var _N2=new T(function(){var _N3=new T(function(){var _N4=new T(function(){var _N5=function(_N6){return _MH(true,function(_N7){return C > 19 ? new F(function(){return A1(_N1,new T2(1,_N6,_N7));}) : (++C,A1(_N1,new T2(1,_N6,_N7)));});};return B(A2(_MF,0,_N5));});return _gF(_MH(false,_N1),_N4);});return B(_qq(function(_N8){var _N9=E(_N8);return (_N9._==2)?(!_aH(_N9.a,_MD))?new T0(2):E(_N3):new T0(2);}));}),_Na=function(_Nb){return E(_N2);};return _gF(new T1(1,function(_Nc){return C > 19 ? new F(function(){return A2(_pj,_Nc,_Na);}) : (++C,A2(_pj,_Nc,_Na));}),new T(function(){return new T1(1,_qX(_MX,_N1));}));};return C > 19 ? new F(function(){return _N0(_MG);}) : (++C,_N0(_MG));},_Nd=function(_Ne,_Nf){return C > 19 ? new F(function(){return _Ng(_Nf);}) : (++C,_Ng(_Nf));},_Ng=function(_Nh){var _Ni=new T(function(){return B(_qq(function(_Nj){var _Nk=E(_Nj);if(_Nk._==1){return C > 19 ? new F(function(){return A1(_Nh,_Nk.a);}) : (++C,A1(_Nh,_Nk.a));}else{return new T0(2);}}));}),_Nl=function(_Nm){return E(_Ni);};return _gF(_gF(new T1(1,function(_Nn){return C > 19 ? new F(function(){return A2(_pj,_Nn,_Nl);}) : (++C,A2(_pj,_Nn,_Nl));}),new T(function(){return B(_ME(_MA,_Nh));})),new T(function(){return new T1(1,_qX(_Nd,_Nh));}));},_No=function(_Np,_Nq){return C > 19 ? new F(function(){return _Ng(_Nq);}) : (++C,_Ng(_Nq));},_Nr=new T(function(){return B(_ME(_No,_hA));}),_Ns=new T(function(){return B(_Ng(_hA));}),_Nt=function(_Nu){return _fE(_Ns,_Nu);},_Nv=new T4(0,function(_Nw,_Nu){return _Nt(_Nu);},function(_Nu){return _fE(_Nr,_Nu);},_No,function(_Nx,_Ny){return C > 19 ? new F(function(){return _ME(_No,_Ny);}) : (++C,_ME(_No,_Ny));}),_Nz=new T(function(){return unCStr(",");}),_NA=function(_NB){return E(E(_NB).c);},_NC=function(_ND,_NE,_NF){var _NG=new T(function(){return _NA(_NE);}),_NH=new T(function(){return B(A2(_NA,_ND,_NF));}),_NI=function(_NJ){var _NK=function(_NL){var _NM=new T(function(){var _NN=new T(function(){return B(A2(_NG,_NF,function(_NO){return C > 19 ? new F(function(){return A1(_NJ,new T2(0,_NL,_NO));}) : (++C,A1(_NJ,new T2(0,_NL,_NO)));}));});return B(_qq(function(_NP){var _NQ=E(_NP);return (_NQ._==2)?(!_aH(_NQ.a,_Nz))?new T0(2):E(_NN):new T0(2);}));}),_NR=function(_NS){return E(_NM);};return new T1(1,function(_NT){return C > 19 ? new F(function(){return A2(_pj,_NT,_NR);}) : (++C,A2(_pj,_NT,_NR));});};return C > 19 ? new F(function(){return A1(_NH,_NK);}) : (++C,A1(_NH,_NK));};return _NI;},_NU=function(_NV,_NW,_NX){var _NY=function(_Nu){return _NC(_NV,_NW,_Nu);},_NZ=function(_O0,_O1){return C > 19 ? new F(function(){return _O2(_O1);}) : (++C,_O2(_O1));},_O2=function(_O3){return _gF(new T1(1,_qX(_NY,_O3)),new T(function(){return new T1(1,_qX(_NZ,_O3));}));};return C > 19 ? new F(function(){return _O2(_NX);}) : (++C,_O2(_NX));},_O4=new T(function(){return B(_ME(function(_O5,_O6){return C > 19 ? new F(function(){return _NU(_Nv,_Nv,_O6);}) : (++C,_NU(_Nv,_Nv,_O6));},_s1));}),_O7=function(_O8,_O9,_Oa){while(1){var _Ob=E(_Oa);if(!_Ob._){return __Z;}else{var _Oc=E(_Ob.a);if(!B(A3(_kP,_O8,_O9,_Oc.a))){_Oa=_Ob.b;continue;}else{return new T1(1,_Oc.b);}}}},_Od=function(_Oe,_Of){var _Og=E(_Of);if(!_Og._){return __Z;}else{var _Oh=E(_Oe);if(_Oh._==3){var _Oi=E(_Oh.b);switch(_Oi._){case 0:return new T1(1,_Oi.a);case 1:return _O7(_hl,new T(function(){return _R(_3Y(E(_Oh.a).b),_fw);}),_Og.a);default:return __Z;}}else{return E(_vI);}}},_Oj=function(_Ok){return _3Y(_3C(_Ok).b);},_Ol=new T(function(){return unCStr("on");}),_Om=function(_On,_Oo){var _Op=E(_Oo);if(!_Op._){return false;}else{var _Oq=_O7(_hl,new T(function(){return B(_Oj(_On));}),_Op.a);if(!_Oq._){return false;}else{return _aH(_Oq.a,_Ol);}}},_Or=function(_Os,_Ot,_Ou){var _Ov=E(_Ou);if(!_Ov._){return false;}else{var _Ow=_O7(_hl,new T(function(){return _3Y(_3C(_Ot).b);}),_Ov.a);if(!_Ow._){return false;}else{var _Ox=_Ow.a,_Oy=E(_Os);if(!_Oy._){return _aH(_Ox,_Oy.a);}else{return _aH(_Ox,_Oy.b);}}}},_Oz=new T(function(){return B(A3(_rr,_rU,0,_hA));}),_OA=function(_OB){var _OC=_fE(_Oz,_OB);return (_OC._==0)?__Z:(E(_OC.b)._==0)?new T1(1,E(_OC.a).a):__Z;},_OD=function(_OE,_OF,_OG){var _OH=E(_OG);switch(_OH._){case 0:var _OI=new T(function(){var _OJ=E(_OF);if(!_OJ._){return __Z;}else{var _OK=_O7(_hl,new T(function(){return _3Y(E(_OH.a).b);}),_OJ.a);if(!_OK._){return __Z;}else{return E(_OK.a);}}});return new T1(1,new T3(1,_OH,_OI,_OE));case 1:var _OL=new T(function(){var _OM=E(_OF);if(!_OM._){return __Z;}else{var _ON=_O7(_hl,new T(function(){return _3Y(E(_OH.a).b);}),_OM.a);if(!_ON._){return __Z;}else{return E(_ON.a);}}});return new T1(1,new T3(2,_OH,_OL,_OE));case 2:var _OO=new T(function(){var _OP=E(_OF);if(!_OP._){return __Z;}else{var _OQ=_O7(_hl,new T(function(){return _3Y(E(_OH.a).b);}),_OP.a);if(!_OQ._){return __Z;}else{return E(_OQ.a);}}});return new T1(1,new T3(3,_OH,_OO,_OE));case 3:var _OR=new T(function(){var _OS=E(_OF);if(!_OS._){return __Z;}else{var _OT=_O7(_hl,new T(function(){return _3Y(E(_OH.a).b);}),_OS.a);if(!_OT._){return __Z;}else{return _OA(_OT.a);}}});return new T1(1,new T4(4,_OH,_OR,new T(function(){return _Od(_OH,_OF);}),_OE));case 4:var _OU=new T(function(){return new T3(5,_OH,_OV,_OE);}),_OV=new T(function(){var _OW=function(_OX){var _OY=E(_OX);if(!_OY._){return new T2(0,_OY,new T(function(){return _Or(_OY,_OH,_OF);}));}else{var _OZ=new T(function(){return _4M(_2m(function(_P0){return _OD(_OU,_OF,_P0);},_OY.c));});return new T3(1,_OY,new T(function(){return _Or(_OY,_OH,_OF);}),_OZ);}};return _2m(_OW,_OH.b);});return new T1(1,_OU);case 5:var _P1=new T(function(){var _P2=E(_OF);if(!_P2._){return __Z;}else{return _O7(_hl,new T(function(){return _3Y(E(_OH.a).b);}),_P2.a);}});return new T1(1,new T3(6,_OH,_P1,_OE));case 6:return __Z;case 7:var _P3=new T(function(){return new T3(7,_OH,_P4,_OE);}),_P4=new T(function(){return _4M(_2m(function(_P0){return _OD(_P3,_OF,_P0);},_OH.c));});return new T1(1,_P3);case 8:var _P5=new T(function(){return new T4(8,_OH,new T(function(){return _Om(_OH,_OF);}),_P6,_OE);}),_P6=new T(function(){return _4M(_2m(function(_P0){return _OD(_P5,_OF,_P0);},_OH.c));});return new T1(1,_P5);case 9:var _P7=new T(function(){return new T3(9,_OH,_P8,_OE);}),_P8=new T(function(){return _4M(_2m(function(_P0){return _OD(_P7,_OF,_P0);},_OH.c));});return new T1(1,_P7);case 10:return new T1(1,new T2(10,_OH,_OE));default:return new T1(1,new T2(11,_OH,_OE));}},_P9=function(_Pa,_Pb,_){var _Pc=__createJSFunc(2,function(_Pd,_){var _Pe=B(A2(E(_Pa),_Pd,_));return _2D;}),_Pf=E(_Pb),_Pg=(function (ev, jq) { jq.resize(ev); }),_Ph=_Pg(_Pc,_Pf);return _Pf;},_Pi=function(_Pj,_Pk,_){var _Pl=__createJSFunc(2,function(_Pm,_){var _Pn=B(A2(E(_Pj),_Pm,_));return _2D;}),_Po=E(_Pk),_Pp=(function (ev, jq) { jq.scroll(ev); }),_Pq=_Pp(_Pl,_Po);return _Po;},_Pr=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,600,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_Ps=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,700,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_Pt=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,500,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_Pu=new T3(0,new T2(6,{_:0,a:__Z,b:new T2(1,new T2(1,100,__Z),0),c:__Z,d:__Z,e:__Z,f:__Z,g:__Z,h:false,i:__Z},__Z),__Z,false),_Pv=new T2(1,_Pu,new T2(1,_2l,new T2(1,_3f,new T2(1,_3c,new T2(1,_Pt,new T2(1,_Pr,new T2(1,_Ps,__Z))))))),_Pw=new T(function(){return (function (jq) { return jq.width(); });}),_Px=new T(function(){return unCStr(".svg-help");}),_Py=new T(function(){return unCStr(".desc-subpane");}),_Pz=new T(function(){return (function (val, jq) { jq.width(val); return jq; });}),_PA=function(_){var _PB=E(_47)(),_PC=E(_Pw)(_PB),_PD=_4b(_Py,_),_PE=Number(_PC),_PF=jsTrunc(_PE),_PG=E(_Pz),_PH=_PG(_PF-790|0,E(_PD)),_PI=_4b(_Px,_),_PJ=_PG(_PF-795|0,E(_PI));return 0;},_PK=function(_PL,_){return _PA(_);},_PM=function(_PN,_){var _PO=(function (label) { console.time(label); }),_PP=_PO(toJSStr(E(_PN)));return _0(_);},_PQ=function(_PR,_){var _PS=(function (label) { console.timeEnd(label); }),_PT=_PS(toJSStr(E(_PR)));return _0(_);},_PU=function(_PV,_){var _PW=new T(function(){var _PX=_fx(_fE(_O4,new T(function(){var _PY=E(_PV);if(!_PY._){return __Z;}else{return E(_PY.a);}})));if(!_PX._){return __Z;}else{if(!E(_PX.b)._){return new T1(1,_PX.a);}else{return __Z;}}}),_PZ=function(_Q0){var _Q1=E(_Q0);if(_Q1._==6){var _Q2=new T(function(){return new T3(0,_Q1,_Q3,false);}),_Q3=new T(function(){return _4M(_2m(function(_Q4){return _OD(_Q2,_PW,_Q4);},_Q1.b));});return new T1(1,_Q2);}else{return __Z;}},_Q5=_2m(_PZ,_9n);if(!_Mk(_Q5)){var _Q6=_PM(_Mn,_),_Q7=new T(function(){return _4M(_Q5);}),_Q8=_LE(_Q7,_),_Q9=_PQ(_Mn,_),_Qa=E(_47),_Qb=_Qa(),_Qc=_Pi(function(_Qd,_){return _4e(_Q7,_);},_Qb,_),_Qe=_Qa(),_Qf=_P9(_PK,_Qe,_),_Qg=_Qa(),_Qh=_4I(_Qg,_),_Qi=_bm(_Pu,_Pv,_);return 0;}else{var _Qj=_4T(_Mo,_);return 0;}},_Qk=new T(function(){return unCStr("#svg_investigator");}),_Ql=new T(function(){return unCStr("#svg_manager");}),_Qm=new T(function(){return unCStr("#svg_steward");}),_Qn=new T(function(){return unCStr("#svg_custodian");}),_Qo=new T(function(){return unCStr("#svg_curator");}),_Qp=new T(function(){return unCStr("#svg_consumer");}),_Qq=new T(function(){return unCStr("#svg_expert");}),_Qr=new T(function(){return unCStr("#svg_producer");}),_Qs=new T(function(){return unCStr("#svg_public");}),_Qt=new T(function(){return unCStr("#svg_secondary");}),_Qu=new T(function(){return unCStr("#svg_primary");}),_Qv=new T(function(){return unCStr("#svg_raw");}),_Qw=new T(function(){return unCStr("margin-top");}),_Qx=new T(function(){return unCStr("body");}),_Qy=new T(function(){return unCStr("div");}),_Qz=function(_,_QA){var _QB=_yk(_Qy,_QA,_),_QC=_4b(_Qx,_),_QD=E(_45)(E(_QC)),_QE=Number(_QD),_QF=jsTrunc(_QE);return _3h(_Qw,_3q(0,_QF+25|0,__Z),E(_QB),_);},_QG=function(_QH,_QI,_){var _QJ=(function (key, jq) { return jq.css(key); }),_QK=_QJ(toJSStr(E(_QH)),_QI);return new T(function(){return String(_QK);});},_QL=new T(function(){return (function (jq) { return jq.height(); });}),_QM=new T(function(){return unCStr("hidden");}),_QN=new T(function(){return unCStr("visibility");}),_QO=new T(function(){return unCStr("visibility");}),_QP=new T(function(){return (function (val, jq) { jq.height(val); return jq; });}),_QQ=new T(function(){return unCStr("visible");}),_QR=function(_QS,_){var _QT=_4b(unAppCStr("#",_QS),_),_QU=_4b(_Qx,_),_QV=E(_QL)(E(_QU)),_QW=Number(_QV),_QX=jsTrunc(_QW),_QY=E(_QP)(_QX,E(_QT)),_QZ=_QG(_QO,_QY,_),_R0=strEq(E(_QZ),"visible");if(!E(_R0)){var _R1=_3h(_QN,_QQ,_QY,_);return _Qz(_,E(_R1));}else{var _R2=_3h(_QN,_QM,_QY,_);return _Qz(_,E(_R2));}},_R3=new T(function(){return (function (f) { jQuery(document).ready(f); });}),_R4=new T(function(){return unCStr("svg_consumer");}),_R5=function(_){return _Ks(_Li,_R4,_);},_R6=function(_R7,_){return _R5(_);},_R8=new T(function(){return unCStr("svg_curator");}),_R9=function(_){var _Ra=_Ks(_Ln,_R8,_),_Rb=_Ks(_Li,_R8,_),_Rc=_Ks(_Lm,_R8,_),_Rd=_Ks(_Ll,_R8,_),_Re=_Ks(_Lk,_R8,_);return _Ks(_Lj,_R8,_);},_Rf=function(_Rg,_){return _R9(_);},_Rh=new T(function(){return unCStr("svg_custodian");}),_Ri=function(_){var _Rj=_Ks(_Lm,_Rh,_),_Rk=_Ks(_Ll,_Rh,_);return _Ks(_Lk,_Rh,_);},_Rl=function(_Rm,_){return _Ri(_);},_Rn=new T(function(){return unCStr("svg_expert");}),_Ro=function(_){var _Rp=_Ks(_Ln,_Rn,_);return _Ks(_Lm,_Rn,_);},_Rq=function(_Rr,_){return _Ro(_);},_Rs=new T(function(){return unCStr("svg_investigator");}),_Rt=function(_){return _Ks(_Lo,_Rs,_);},_Ru=function(_Rv,_){return _Rt(_);},_Rw=new T(function(){return unCStr("svg_manager");}),_Rx=function(_){var _Ry=_Ks(_Lp,_Rw,_),_Rz=_Ks(_Ln,_Rw,_),_RA=_Ks(_Lm,_Rw,_),_RB=_Ks(_Ll,_Rw,_),_RC=_Ks(_Lk,_Rw,_);return _Ks(_Lj,_Rw,_);},_RD=function(_RE,_){return _Rx(_);},_RF=new T(function(){return unCStr("arrow_2_4");}),_RG=new T(function(){return unCStr("arrow_2_3");}),_RH=new T(function(){return unCStr("svg_secondary");}),_RI=new T(function(){return unCStr("box_4_2");}),_RJ=new T(function(){return unCStr("svg_primary");}),_RK=function(_){var _RL=_Ks(_Ln,_RJ,_),_RM=_Ks(_RI,_RH,_),_RN=_Ks(_RG,_RJ,_);return _Ks(_RF,_RJ,_);},_RO=function(_RP,_){return _RK(_);},_RQ=new T(function(){return unCStr("svg_producer");}),_RR=function(_){return _Ks(_Lp,_RQ,_);},_RS=function(_RT,_){return _RR(_);},_RU=new T(function(){return unCStr("svg_public");}),_RV=new T(function(){return unCStr("arrow_H_3");}),_RW=function(_){return _Ks(_RV,_RU,_);},_RX=function(_RY,_){return _RW(_);},_RZ=new T(function(){return unCStr("box_4_3");}),_S0=new T(function(){return unCStr("arrow_1_4");}),_S1=new T(function(){return unCStr("arrow_1_2");}),_S2=new T(function(){return unCStr("svg_raw");}),_S3=function(_){var _S4=_Ks(_Lp,_S2,_),_S5=_Ks(_S1,_S2,_),_S6=_Ks(_S0,_S2,_);return _Ks(_RZ,_S2,_);},_S7=function(_S8,_){return _S3(_);},_S9=new T(function(){return unCStr("arrow_3_4");}),_Sa=function(_){var _Sb=_Ks(_Li,_RH,_),_Sc=_Ks(_Lm,_RH,_),_Sd=_Ks(_RV,_RH,_);return _Ks(_S9,_RH,_);},_Se=function(_Sf,_){return _Sa(_);},_Sg=new T(function(){return unCStr("svg_steward");}),_Sh=function(_){var _Si=_Ks(_Lp,_Sg,_),_Sj=_Ks(_Ln,_Sg,_),_Sk=_Ks(_Li,_Sg,_),_Sl=_Ks(_Lm,_Sg,_),_Sm=_Ks(_Ll,_Sg,_),_Sn=_Ks(_Lk,_Sg,_);return _Ks(_Lj,_Sg,_);},_So=function(_Sp,_){return _Sh(_);},_Sq=function(_){var _Sr=function(_){var _Ss=function(_St,_){return C > 19 ? new F(function(){return _QR(new T(function(){var _Su=String(E(_St));return fromJSStr(_Su);}),_);}) : (++C,_QR(new T(function(){var _Su=String(E(_St));return fromJSStr(_Su);}),_));},_Sv=__createJSFunc(2,_Ss),_Sw=(function(s,f){Haste[s] = f;}),_Sx=_Sw("overlay",_Sv),_Sy=__createJSFunc(2,function(_Sz,_){var _SA=_bm(_Pu,_Pv,_);return _2D;}),_SB=(function(s,f){Haste[s] = f;}),_SC=_SB("toVision",_Sy),_SD=__createJSFunc(2,function(_SE,_){var _SF=_bm(_2l,_Pv,_);return _2D;}),_SG=(function(s,f){Haste[s] = f;}),_SH=_SG("toAction",_SD),_SI=__createJSFunc(2,function(_SJ,_){var _SK=_bm(_3f,_Pv,_);return _2D;}),_SL=(function(s,f){Haste[s] = f;}),_SM=_SL("toLifecycle",_SI),_SN=__createJSFunc(2,function(_SO,_){var _SP=_bm(_3c,_Pv,_);return _2D;}),_SQ=(function(s,f){Haste[s] = f;}),_SR=_SQ("toData",_SN),_SS=__createJSFunc(2,function(_ST,_){var _SU=_bm(_Pt,_Pv,_);return _2D;}),_SV=(function(s,f){Haste[s] = f;}),_SW=_SV("toRoles",_SS),_SX=__createJSFunc(2,function(_SY,_){var _SZ=_bm(_Pr,_Pv,_);return _2D;}),_T0=(function(s,f){Haste[s] = f;}),_T1=_T0("toMQuestionnaire",_SX),_T2=__createJSFunc(2,function(_T3,_){var _T4=_bm(_Ps,_Pv,_);return _2D;}),_T5=(function(s,f){Haste[s] = f;}),_T6=_T5("toTQuestionnaire",_T2),_T7=_4b(_Qv,_),_T8=_cK(_S7,_T7,_),_T9=_4b(_Qu,_),_Ta=_cK(_RO,_T9,_),_Tb=_4b(_Qt,_),_Tc=_cK(_Se,_Tb,_),_Td=_4b(_Qs,_),_Te=_cK(_RX,_Td,_),_Tf=_4b(_Qr,_),_Tg=_cK(_RS,_Tf,_),_Th=_4b(_Qq,_),_Ti=_cK(_Rq,_Th,_),_Tj=_4b(_Qp,_),_Tk=_cK(_R6,_Tj,_),_Tl=_4b(_Qo,_),_Tm=_cK(_Rf,_Tl,_),_Tn=_4b(_Qn,_),_To=_cK(_Rl,_Tn,_),_Tp=_4b(_Qm,_),_Tq=_cK(_So,_Tp,_),_Tr=_4b(_Ql,_),_Ts=_cK(_RD,_Tr,_),_Tt=_4b(_Qk,_),_Tu=_cK(_Ru,_Tt,_),_Tv=_4b(_3e,_),_Tw=E(_3d)(E(_Tv)),_Tx=B(A(_2J,[new T2(0,new T5(0,new T5(0,new T2(0,_p,_l),_t,_g,_v,_b),_2h,_v,_t,_2f),_1),_3,_3,new T2(0,_9,_7),1,_3g,new T2(1,new T2(0,"respondent_key",new T(function(){var _Ty=String(_Tw);return toJSStr(fromJSStr(_Ty));})),__Z),_PU,_]));return _2D;},_Tz=__createJSFunc(0,_Sr),_TA=E(_R3)(_Tz);return _0(_);},_TB=function(_){return _Sq(_);};
var hasteMain = function() {B(A(_TB, [0]));};window.onload = hasteMain;