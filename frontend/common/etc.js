//@ts-check
// infrastructure stuff
//

class ArrayFuncs {
    static last(/** @type {Array} */ arr) { return arr[arr.length - 1]; }
    static flatten(/** @type {Array} */ arr) { return [].concat.apply([], arr); }
    static findLast(/** @type {Array} */ arr, /** @type {(el: any) => boolean} */ p) {
        var r;
        for (let i = arr.length; i > 0; ) if (p(r = arr[--i])) return r;
    }
    static equals(/** @type {Array} */ arr1, /** @type {Array} */ arr2) {
        return arreq_deep(arr1, arr2);
    }
}
//@ts-ignore  [these should actually be removed once we are certain they are not called]
Array.prototype.last     = function() { return this[this.length-1]; };
//@ts-ignore
Array.prototype.flatten  = function() { return [].concat.apply([], this); };
//@ts-ignore
Array.prototype.findLast = function(p) { var r; for (let i = this.length; i > 0; )
                                                    if (p(r = this[--i])) return r; }
//@ts-ignore
Array.prototype.equals   = function(other) { return arreq_deep(this, other); }
Object.defineProperty(Array.prototype, "last",     {enumerable: false});
Object.defineProperty(Array.prototype, "flatten",  {enumerable: false});
Object.defineProperty(Array.prototype, "findLast", {enumerable: false});
Object.defineProperty(Array.prototype, "equals",   {enumerable: false});

function arreq_deep(arr1, arr2) {  /* adapted from 'array-equal' */
    var length = arr1.length
    if (!arr2 || length !== arr2.length) return false
    for (var i = 0; i < length; i++) {
        let e1 = arr1[i], e2 = arr2[i];
        if (!(Array.isArray(e1) && Array.isArray(e2) ? arreq_deep(e1, e2) : e1 === e2))
            return false
    }
    return true
}

/* @todo use `merge-options` */
function copyOptions(obj, target) {
    if (typeof obj !== 'object' || obj instanceof Array) return obj;
    if (typeof target !== 'object' || target instanceof Array) target = {};
    for (var prop in obj) {
        if (obj.hasOwnProperty(prop)) {
            target[prop] = copyOptions(obj[prop], target[prop]);
        }
    }
    return target;
}

const isMac = typeof navigator === 'undefined' ? false
    : /\bMac\b/.test(navigator.userAgent);

export { ArrayFuncs, arreq_deep, copyOptions, isMac }
