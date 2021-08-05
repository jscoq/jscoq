const webpack = require('webpack');

module.exports = [
{
  name: 'cli',
  target: 'node',
  entry: './coq-jslib/cli.ts',
  mode: 'development',
  devtool: "source-map",
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
    path: __dirname  // should be run by Dune in _build/*
  },
  plugins: [
    new webpack.BannerPlugin({banner: '#!/usr/bin/env node', raw: true}),
    new webpack.optimize.LimitChunkCountPlugin({maxChunks: 1})
  ],
  node: false
}
];
