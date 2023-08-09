//@ts-check
// infrastructure stuff
//

class ArrayFuncs {
    static flatten(/** @type {Array} */ arr) { return [].concat.apply([], arr); }
}

//@ts-ignore
Array.prototype.flatten  = function() { return [].concat.apply([], this); };
Object.defineProperty(Array.prototype, "flatten",  {enumerable: false});

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

export { ArrayFuncs, arreq_deep, copyOptions, isMac }
