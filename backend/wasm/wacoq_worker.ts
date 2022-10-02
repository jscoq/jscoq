import { IcoqPod } from './core';



function postMessage(msg) {
    (<any>self).postMessage(msg);
}


async function main() {
    var icoq = new IcoqPod();

    postMessage(['Starting']);
    icoq.on('message', postMessage);
    icoq.on('progress', ev => postMessage(['LibProgress', ev]));

    addEventListener('message', (msg) => {
        console.log(msg.data);
        icoq.command(msg.data);
    });

    await icoq.boot();

    postMessage(['Boot']);

    Object.assign(global, {icoq});
}

main();