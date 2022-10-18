"use strict";
import { arreq_deep } from '../frontend/common/etc.js'; /** @oops need this func which happens to be in the frontend */

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
        this.tags = [];
    }

    toString() { return this.toStrings().join('.'); }
    toStrings() { return [...this.prefix, this.label]; }

    equals(other) {
        return other instanceof CoqIdentifier &&
            arreq_deep(this.prefix, other.prefix) && this.label === other.label;
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
     * @param {{dirpath: ['DirPath', any[]], basename: string[]}} fp serialized form of `full_path`.
     */
    static ofFullPath(fp) {
        return new CoqIdentifier(
            this._dirpath(fp.dirpath), this._idToString(fp.basename));
    }

    /**
     * Constructs an identifier from a `qualified_name`. This type comes from
     * the worker protocol, and may contain a dirpath as well as a module path.
     * @see inspect.ml
     * @param {{prefix : {dp: ['DirPath', any[]], mod_ids: any[]},
     *          basename: string[]}} qn serialized form of `qualified_name` (from SearchResults).
     */
    static ofQualifiedName(qn) {
        /**/ console.assert(qn.prefix.dp[0] === 'DirPath') /**/
        return new CoqIdentifier(
            qn.prefix.dp[1].slice().reverse()
                .concat(qn.prefix.mod_ids).map(this._idToString),
            this._idToString(qn.basename));
    }

    /**
     * Constructs an identifier from a serialized `Qualid` (`Ser_Qualid`).
     */
    static ofQualid(qid) {
        /**/ console.assert(qid[0] == 'Ser_Qualid') /**/
        return new CoqIdentifier(
            this._dirpath(qid[1]), this._idToString(qid[2]));
    }

    /**
     * @param {['DirPath', any[]]} dp serialized `DirPath`
     * @returns {string[]}
     */
    static _dirpath(dp) {
        /**/ console.assert(dp[0] == 'DirPath') /**/
        return dp[1].slice().reverse().map(this._idToString);
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
            if (arreq_deep(this.prefix.slice(0, prefix.length), prefix))
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
