import path from "path";
import os from "os";
import {createRequire} from "module";
const __dirname = path.resolve('.'),
    __tmpdir = path.resolve(os.tmpdir()),
    require = createRequire(import.meta.url);

export default (env, argv) => [
{
        name: 'gist',
        entry: './gist.js',
        output: {
            filename: 'gist.browser.js',
            path: path.join(__dirname, 'dist-webpack/addon'),
            library: {
                name: 'gist_save_load',
                type: 'var',
            },
        },
        resolve: {
            fallback: {
                "fs": false,
                "constants": require.resolve("constants-browserify"),
                "path": require.resolve("path-browserify"),
                "util": require.resolve("util/"),
                "assert": require.resolve("assert/")
            }
        },
    }
]