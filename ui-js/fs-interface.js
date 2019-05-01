/**
 * An abstraction layer that separates Coq build utility classes from the
 * actual filesystem implementation, in much a similar way to how MlNodeDevice
 * and MlFakeDevice operate in js_of_ocaml.
 * 
 * This layer allows such classes to function with other sources for files,
 * such as Zip bundles of .v/.vo entries.
 * 
 * In this case, however, the interface has to adhere to JavaScript standards.
 * The substituted interfaces are:
 * - fs: readFileSync, statSync
 * - path: join, isAbsolute
 * - glob: sync
 */

const fs = require('fs'),
      glob = require('glob'),
      path = require('path')

const fsif_native = {fs, path, glob};


module.exports = {fsif_native}
