const path = require('path');
const webpack = require('webpack');

// `--env readable` writes the published mod/main.js: not minified and without a source map, so that the
// code stays readable. The other builds are upstream Cookie Monster's.
module.exports = function (env) {
  const readable = !!env.readable;
  return {
    mode: 'production',
    devtool: readable ? false : env.minimize ? 'source-map' : 'inline-source-map',
    optimization: {
      minimize: !readable && !!env.minimize,
    },
    entry: './src/CookieMonster.js',
    resolve: { symlinks: false },
    output: readable
      ? { filename: 'main.js', path: path.resolve(__dirname, '../../mod') }
      : {
          filename: env.finalfile ? 'CookieMonster.js' : 'CookieMonsterDev.js',
          path: path.resolve(__dirname, 'dist'),
        },
    plugins: readable
      ? []
      : [
          new webpack.SourceMapDevToolPlugin({
            filename:
              env.finalfile && env.minimize ? 'CookieMonster.js.map' : 'CookieMonsterDev.js.map',
            publicPath: 'https://cookiemonsterteam.github.io/CookieMonster/dist/',
            fileContext: 'public',
          }),
        ],
  };
};
