const webpack = require('webpack'),
      fs = require('fs'),
      path = require('path'),
      { VueLoaderPlugin } = require('vue-loader');

const
  basics = (argv) => ({
    mode: 'development',
    devtool: argv.mode !== 'production' ? "source-map" : undefined,
    stats: {
      hash: false, version: false, modules: false  // reduce verbosity
    },
    performance: {
      maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
    },
  }),
  ts = {
    test: /\.tsx?$/,
    use: 'ts-loader',
    exclude: /node_modules/,
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
  cliPlugins = (scriptName) => [
    new webpack.BannerPlugin({banner: '#!/usr/bin/env node', raw: true}),
    new webpack.optimize.LimitChunkCountPlugin({maxChunks: 1}),
    function() {
      this.hooks.afterDone.tap('chmod', () => fs.chmodSync(scriptName, 0755));
    }
  ],
  resolve = {
    extensions: [ '.tsx', '.ts', '.js' ]
  },
  output = (dirname, filename) => ({
    filename, path: path.join(__dirname, dirname)
  });

module.exports = (env, argv) => [
/**
 * jsCoq CLI
 * (note: the waCoq CLI is located in package `wacoq-bin`)
 */
{
  name: 'cli',
  target: 'node',
  entry: './coq-jslib/cli.ts',
  ...basics(argv),
  module: {
    rules: [ts]
  },
  externals: {  /* do not bundle the worker */
    '../coq-js/jscoq_worker.bc.js': 'commonjs2 ../coq-js/jscoq_worker.bc.js',
    'wacoq-bin/dist/subproc': 'undefined',
    'cross-spawn': 'commonjs2 cross-spawn'
  },
  resolve,
  output: output('dist', 'cli.js'),
  plugins: cliPlugins('dist/cli.js'),
  node: false
},
/**
 * CodeMirror 6
 */
{
  name: 'editor-base',
  entry: './ui-js/editor-base.ts',
  ...basics(argv),
  module: {
    rules: [ts]
  },
  resolve,
  output: {
    filename: 'cm6-editor-base.js',
    path: path.join(__dirname, 'dist'),
    library: 'cm6',
    libraryTarget: 'umd'
  }
},
/**
 * Multi-file Project UI
 */
{
  name: 'ide-project',
  entry: './ui-js/ide-project.js',
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
  entry: './ui-js/addon/collab.js',
  ...basics(argv),
  output: {
    filename: 'collab.browser.js',
    path: path.join(__dirname, 'dist/addon'),
    library: 'addonCollab',
    libraryTarget: 'umd'
  },
  module: {
    rules: [css, imgs]
  }
}
];
