import fs from 'fs';
import path from 'path';

type FSInterface = {
    fs: typeof fs
    path: typeof path
}


const fsif_native: FSInterface = {
    fs: tryRequireFs(),
    path: require('path')
}

function tryRequireFs() { 
    try { return require('fs'); } catch (e) { return {}; } 
}


export { FSInterface, fsif_native }
