const webpack = require('webpack'),
      path = require('path'),
      VueLoaderPlugin = require('vue-loader/lib/plugin');

module.exports = (env, argv) => [{
  name: 'ide-project',
  mode: argv.mode || 'development',
  entry: './ide-project.js',
  devtool: argv.mode !== 'production' ? "source-map" : undefined,
  stats: {
    hash: false, version: false, modules: false  // reduce verbosity
  },
  performance: {
    maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
  },
  output: {
    filename: 'ide-project.browser.js',
    path: __dirname,
    library: 'ideProject',
    libraryTarget: 'umd',
    publicPath: '/ui-js/'
  },
  externals: {
    fs: 'empty', child_process: 'empty'
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
        use: ['file-loader']
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
{
  name: 'collab',
  mode: 'development',
  entry: './addon/collab.js',
  devtool: argv.mode !== 'production' ? "source-map" : undefined,
  stats: {
    hash: false, version: false, modules: false  // reduce verbosity
  },
  performance: {
    maxAssetSize: 1e6, maxEntrypointSize: 1e6   // 250k is too small
  },
  output: {
    filename: 'collab.browser.js',
    path: path.join(__dirname, 'addon'),
    library: 'addonCollab',
    libraryTarget: 'umd',
    publicPath: '/ui-js/addon/'
  },
  module: {
    rules: [
      {
        test: /\.css$/i,
        use: ['style-loader', 'css-loader'],
      },
      {
        test: /\.(png|jpe?g|gif)$/i,
        use: ['file-loader']
      }
    ]
  }
}];
