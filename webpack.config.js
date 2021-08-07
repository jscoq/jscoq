const webpack = require('webpack'),
      fs = require('fs'),
      path = require('path'),
      { VueLoaderPlugin } = require('vue-loader');

module.exports = (env, argv) => [
/**
 * jsCoq CLI
 * (note: the waCoq CLI is located in package `wacoq-bin`)
 */
{
  name: 'cli',
  target: 'node',
  entry: './coq-jslib/cli.ts',
  mode: 'development',
  devtool: argv.mode !== 'production' ? "source-map" : undefined,
  stats: {
    hash: false, version: false, modules: false  // reduce verbosity
  },
  module: {
    rules: [
      {
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: /node_modules/,
      },
    ],
  },
  externals: {  /* do not bundle the worker */
    './coq-js/jscoq_worker.bc.js': 'commonjs2 ./coq-js/jscoq_worker.bc.js',
    'wacoq-bin/dist/subproc': 'commonjs2'
  },
  resolve: {
    extensions: [ '.tsx', '.ts', '.js' ],
  },
  output: {
    filename: 'cli.js',
    path: path.join(__dirname, 'dist')
  },
  plugins: [
    new webpack.BannerPlugin({banner: '#!/usr/bin/env node', raw: true}),
    new webpack.optimize.LimitChunkCountPlugin({maxChunks: 1}),
    function() {
      this.hooks.afterDone.tap('chmod', () => fs.chmodSync('dist/cli.js', 0755));
    }
  ],
  node: false
},
/**
 * Multi-file Project UI
 */
{
  name: 'ide-project',
  mode: 'development',
  entry: './ui-js/ide-project.js',
  devtool: argv.mode !== 'production' ? "source-map" : undefined,
  stats: {
    hash: false, version: false, modules: false  // reduce verbosity
  },
  performance: {
    maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
  },
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
    rules: [
      {
        test: /\.tsx?$/,
        use: 'ts-loader',
        exclude: /node_modules/,
      },
      {
        test: /\.css$/i,
        use: ['style-loader', 'css-loader'],
      },
      {
        test: /\.scss$/i,  /* Vue.js has some */
        use: ['style-loader', 'css-loader', 'sass-loader'],
      },
      {
        test: /\.(png|jpe?g|gif)$/i,
        loader: 'file-loader',
        options: {
          outputPath: 'ide-project-images',
        }
      },
      {
        test: /\.vue$/,
        use: 'vue-loader'
      }
    ],
  },
  resolve: {
    extensions: [ '.tsx', '.ts', '.js' ],
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
  mode: 'development',
  entry: './ui-js/addon/collab.js',
  devtool: argv.mode !== 'production' ? "source-map" : undefined,
  stats: {
    hash: false, version: false, modules: false  // reduce verbosity
  },
  performance: {
    maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
  },
  output: {
    filename: 'collab.browser.js',
    path: path.join(__dirname, '../dist/addon'),
    library: 'addonCollab',
    libraryTarget: 'umd'
  },
  module: {
    rules: [
      {
        test: /\.css$/i,
        use: ['style-loader', 'css-loader'],
      },
      {
        test: /\.(png|jpe?g|gif)$/i,
        loader: 'file-loader',
        options: {
          outputPath: 'collab-images',
        }
      }
    ]
  }
}
];
