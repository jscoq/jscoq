"use strict";
/**
 * Coq Identifier
 *
 * @class CoqIdentifier
 */
export class CoqIdentifier {

    /**
     * @param {Array<string>} prefix
     * @param {string} label
     */
    constructor(prefix, label) {
        this.prefix = prefix;
        this.label = label;
    }

    toString() { return [...this.prefix, this.label].join('.'); }

    equals(other) {
        return other instanceof CoqIdentifier &&
            this.prefix.equals(other.prefix) && this.label === other.label;
    }

    /**
     * Constructs an identifier from a Coq `Names.KerName.t`.
     * @param {array} param0 serialized form of `KerName`.
     */
    static ofKerName([kername, modpath, label]) {
        /**/ console.assert(kername === 'KerName') /**/
        var modsuff = [];
        while (modpath[0] == 'MPdot') {
            modsuff.push(modpath[2]);
            modpath = modpath[1];
        }
        /**/ console.assert(modpath[0] === 'MPfile'); /**/
        /**/ console.assert(modpath[1][0] === 'DirPath'); /**/
        return new CoqIdentifier(
            modpath[1][1].slice().reverse().map(this._idToString).concat(modsuff),
            this._idToString(label));
    }

    /**
     * Constructs an identifier from a `Libnames.full_path`.
     * @param {{dirpath: string[], basename: string[]}} fp serialized form of `full_path`.
     */
    static ofFullPath(fp) {
        /**/ console.assert(fp.dirpath[0] === 'DirPath') /**/
        return new CoqIdentifier(
            fp.dirpath[1].slice().reverse().map(this._idToString),
            this._idToString(fp.basename));
    }

    /**
     * Constructs an identifier from a `qualified_name`. This type comes from
     * the worker protocol, and may contain a dirpath as well as a module path.
     * @see inspect.ml
     * @param {{prefix : { dp: string[] }, basename: string[]}} qn serialized form of `qualified_name` (from SearchResults).
     */
    static ofQualifiedName(qn) {
        /**/ console.assert(qn.prefix.dp[0] === 'DirPath') /**/
        return new CoqIdentifier(
            qn.prefix.dp[1].slice().reverse()
                .concat(qn.prefix.mod_ids).map(this._idToString),
            this._idToString(qn.basename));
    }

    /**
     * @param {string[]} id
     */
    static _idToString(id) {
        /**/ console.assert(id[0] === 'Id') /**/
        return id[1];
    }

    dequalify(dirpaths) {
        for (let prefix of dirpaths) {
            if (this.prefix.slice(0, prefix.length).equals(prefix))
                return this.ltrunc(prefix.length)
        }
        return this;
    }

    ltrunc(n) {
        var d = new CoqIdentifier(this.prefix.slice(n), this.label);
        d.tags = this.tags;
        return d;
    }
}
