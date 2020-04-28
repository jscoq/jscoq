import fs from 'fs';
import path from 'path';

type FSInterface = {
    fs: typeof fs
    path: typeof path
}


const fsif_native = {
    fs: (0||require)('fs'),
    path: (0||require)('path')
}



export { FSInterface, fsif_native }
