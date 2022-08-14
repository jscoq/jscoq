var copyOptions = function(obj, target) {
    if (typeof obj !== 'object' || obj instanceof Array) return obj;
    if (typeof target !== 'object' || target instanceof Array) target = {};
    for (var prop in obj) {
        if (obj.hasOwnProperty(prop)) {
            target[prop] = copyOptions(obj[prop], target[prop]);
        }
    }
    return target;
}

var JsCoq;
