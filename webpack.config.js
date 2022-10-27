import os from 'os';
import webpack from 'webpack';
import fs from 'fs';
import path from 'path';
import { createRequire } from 'module';

import { VueLoaderPlugin } from 'vue-loader';
import TerserPlugin from 'terser-webpack-plugin';

const __dirname = path.resolve('.'),
      __tmpdir = path.resolve(os.tmpdir()),
      require = createRequire(import.meta.url);

const
  basics = (argv) => ({
    mode: 'development',
    devtool: argv.mode !== 'production' ? "source-map" : undefined,
    stats: {
      hash: false, version: false, modules: false  // reduce verbosity
    },
    cache: {
      type: 'filesystem',
      cacheDirectory: path.resolve(__tmpdir, '.webpack_cache')
    },
    performance: {
      maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
    }
  }),
  ts = {
    test: /\.tsx?$/,
    loader: 'ts-loader',
    options: { allowTsInNodeModules: true }
  },
  css = {
    test: /\.css$/i,
    use: ['style-loader', 'css-loader'],
  },
  scss = {
    test: /\.scss$/i,  /* Vue.js has some */
    use: ['style-loader', 'css-loader', 'sass-loader'],
  },
  imgs = {
    test: /\.(png|jpe?g|gif)$/i,
    loader: 'file-loader',
    options: {
      outputPath: 'ide-project-images',
    }
  },
  vuesfc = {
    test: /\.vue$/,
    use: 'vue-loader'
  },
  shims = {
    modules: {
      path: 'path-browserify',
      stream: 'stream-browserify',
      tty: false, url: false, worker_threads: false,
      fs: false, crypto: false
    },
    plugins: [
        new webpack.DefinePlugin({process: {browser: true, env: {}, cwd: () => "/"}}),
        new webpack.ProvidePlugin({Buffer: ['buffer', 'Buffer']})
        //new webpack.ProvidePlugin({process: 'process/browser.js',
        //  Buffer: ['buffer', 'Buffer']})]
    ]
  },
  cliPlugins = (scriptName) => [
    new webpack.BannerPlugin({banner: '#!/usr/bin/env node', raw: true}),
    new webpack.optimize.LimitChunkCountPlugin({maxChunks: 1}),
    function() {
      this.hooks.afterDone.tap('chmod', () => fs.chmodSync(scriptName, 0o755));
    }
  ],
  // resources that only make sense in browser context
  browserOnly = /\/codemirror\/|(\/dist\/lib.js$)|(coq-mode.js$)|(company-coq.js$)/,
  resolve = {
    extensions: [ '.tsx', '.ts', '.js', '.cjs' ]
  },
  output = (dirname, filename) => ({
    filename, path: path.join(__dirname, dirname)
  });

export default (env, argv) => [
/**
 * jsCoq CLI
 * (note: the waCoq CLI is located in package `wacoq-bin`)
 */
{
  name: 'cli',
  target: 'node',
  entry: './frontend/cli/cli.ts',
  ...basics(argv),
  module: {
    rules: [ts]
  },
  externals: [
    {  /* do not bundle the worker */
      '../backend/jsoo/jscoq_worker.bc.cjs': 'commonjs2 ../backend/jsoo/jscoq_worker.bc.cjs',
      'wacoq-bin/dist/subproc': 'undefined',
      'cross-spawn': 'commonjs2 cross-spawn'
    },
    /* filter out browser-only modules */
    ({context, request}, callback) => {
      if (request.match(browserOnly)) callback(null, '{}')
      else callback();
    }
  ],
  resolve,
  output: output('dist', 'cli.cjs'),
  plugins: cliPlugins('dist/cli.cjs'),
  node: false
},
/**
 * Package libs for browser modules.
 */
{
  name: 'lib',
  entry: './frontend/classic/js/lib.js',
  ...basics(argv),
  resolve,
  output: {...output('dist', 'lib.js'), libraryTarget: 'module'},
  optimization: {
    minimizer: [
      new TerserPlugin({  /* this is a hack because Ronin's Syncpad checks the class name */
        terserOptions: { keep_fnames: /^CodeMirror$/ }
      })  
    ]
  },
  experiments: {
    outputModule: true
  }
},
/**
 * Package backend for wider-comsumption.
 */
 {
  name: 'wacoq_worker',
  target: 'webworker',
  entry: './backend/wasm/wacoq_worker.ts',
  ...basics(argv),
  module: {
    rules: [ts]
  },
  resolve: {...resolve, fallback: shims.modules},
  output: output('dist', 'wacoq_worker.js'),
  plugins: shims.plugins
},
/**
 * Package backend for wider-comsumption.
 */
{
  name: 'backend',
  entry: './backend/index.ts',
  ...basics(argv),
  module: {
    rules: [ts]
  },
  resolve,
  output: {...output('dist', 'backend.js'), libraryTarget: 'module'},
  experiments: {
    outputModule: true
  }
},
/**
 * Package frontend for wider-comsumption and sanity
 */
{
  name: 'frontend',
  entry: './frontend/classic/js/index.js',
  dependencies: [ 'lib' ],
  ...basics(argv),
  module: {
    rules: [ts]
  },
  resolve,
  output: {...output('dist', 'frontend.js'), libraryTarget: 'module'},
  experiments: {
    outputModule: true
  }
},
/**
 * Multi-file Project UI
 */
{
  name: 'ide-project',
  entry: './frontend/classic/js/ide-project.js',
  ...basics(argv),
  output: {
    filename: 'ide-project.browser.js',
    path: path.join(__dirname, 'dist'),
    library: 'ideProject',
    libraryTarget: 'umd'
  },
  externals: {
    fs: 'commonjs2 fs', child_process: 'commonjs2 child_process',
    'wacoq-bin/dist/subproc': 'commonjs2'
  },
  module: {
    rules: [ts, css, scss, imgs, vuesfc]
  },
  resolve: {
    ...resolve,
    fallback: { "stream": require.resolve("stream-browserify") }
  },
  plugins: [new VueLoaderPlugin(),
            new webpack.ProvidePlugin({process: 'process/browser'})]
},
/**
 * Collaboration plugin
 * (Hastebin)
 */
{
  name: 'collab',
  entry: './frontend/classic/js/addon/collab/index.ts',
  ...basics(argv),
  output: {
    filename: 'collab.browser.js',
    path: path.join(__dirname, 'dist/addon'),
    library: 'addonCollab',
    libraryTarget: 'umd'
  },
  externals: {
    './codemirror6-adapter.js': '{}' /* cm6 (from firepad); not used */
  },
  resolve: {
    ...resolve,
    fallback: {
      "fs": false,
      "constants": require.resolve("constants-browserify"),
      "path": require.resolve("path-browserify"),
      "util": require.resolve("util/"),
      "assert": require.resolve("assert/")
    }
  },
  module: {
    rules: [ts, css, imgs, vuesfc],
    unknownContextCritical: false  /* for `randombytes` */
  },
  optimization: {
    splitChunks: {
      cacheGroups: {
        roninVendor: {
          /* assume all async-import'ed modules are Ronin; there are too many to list */
          name: 'ronin-p2p'
        }
      }
    }
  },
  plugins: shims.plugins
           //[new webpack.ProvidePlugin({process: 'process/browser.js',
           //                            Buffer: ['buffer', 'Buffer']})]
}
];
