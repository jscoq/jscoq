import { IcoqPod } from './core';



function postMessage(msg) {
    (<any>self).postMessage(msg);
}


async function main() {
    /** @note when serving from source tree, the `node_modules` ref works by chance */
    var icoq = new IcoqPod('../backend/wasm', '../node_modules');

    postMessage(['Starting']);
    icoq.on('message', postMessage);
    icoq.on('progress', ev => postMessage(['LibProgress', ev]));

    addEventListener('message', (msg) => {
        icoq.command(msg.data);
    });

    await icoq.boot();

    postMessage(['Boot']);

    Object.assign(global, {icoq});
}

main();