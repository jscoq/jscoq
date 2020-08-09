
module.exports = {
  name: 'ide-project',
  mode: 'development',
  entry: './ide-project.js',
  devtool: "source-map",
  output: {
    filename: 'ide-project.browser.js',
    path: __dirname,
    library: 'ideProject',
    libraryTarget: 'umd',
    publicPath: '/ui-js/'
  },
  node: {
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
      }
    ],
  },
  resolve: {
    extensions: [ '.tsx', '.ts', '.js' ],
  }
};
