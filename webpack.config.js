import os from 'os';
import webpack from 'webpack';
import path from 'path';
import { createRequire } from 'module';
import { VueLoaderPlugin } from 'vue-loader';

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
      path: 'stream-browserify',
      stream: 'stream-browserify',
      tty: false, url: false, worker_threads: false,
      fs: false, crypto: false
    },
    plugins: [
        new webpack.DefinePlugin({process: {browser: true, env: {}, cwd: () => "/"}}),
        new webpack.ProvidePlugin({Buffer: ['buffer', 'Buffer']})
    ]
  },
  // resources that only make sense in browser context
  resolve = {
    extensions: [ '.tsx', '.ts', '.js', '.cjs' ]
  },
  output = (dirname, filename) => ({
    filename, path: path.join(__dirname, dirname)
  });

export default (env, argv) => [

/**
 * Multi-file Project UI
 */
{
  name: 'ide-project',
  entry: './frontend/classic/js/ide-project.js',
  ...basics(argv),
  output: {
    filename: 'ide-project.browser.js',
    path: path.join(__dirname, 'dist-webpack'),
    library: 'ideProject',
    libraryTarget: 'umd'
  },
  externals: {
    fs: 'commonjs2 fs',
    child_process: 'commonjs2 child_process',
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
    path: path.join(__dirname, 'dist-webpack/addon'),
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
