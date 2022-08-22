import { Url } from "url";
import { Coq } from "./types";

namespace Package {
  namespace Param {
    type Info = { lib_path: Url, pkgs: string[] }
    type Load = { lib_path: Url, pkg: string }
  }
}

namespace Stm {
  export type sid = number
  export type Add = [sid, sid, string, boolean]
}

namespace JsCoq {

  namespace Debug {
    export interface Config {
      coq: boolean;
      stm: boolean;
     }
  }

  interface Options {
    implicit_libs: boolean;
    coq_options: Coq.Options;
    debug: Debug.Config;
    lib_path: Coq.LoadPath;
  }
  interface DocumentOptions {
    top_name: string;
    lib_init: string[];
    mode: Coq.TopMode;
  }
  
  interface Query { }

  namespace Param {
    type Init = Options
    type NewDoc = DocumentOptions
    type Add = Stm.Add
    type Cancel = Stm.sid
    type Exec = Stm.sid
    type Query = [Stm.sid, number, Query]
    type Ast = Stm.sid
    type Register = string
    type Put = [string, string]
    type ReassureLoadPath = Coq.LoadPath
  }

  namespace Answer {

  }
}

export abstract class CoqWorker {
  constructor() {}
  abstract sendMessage() : void
}