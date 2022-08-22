// Coq basic types, as exported by ppx_deriving_yojson

import assert from "assert";

export namespace Coq {

    // Coq Identifier
    namespace Names {

        export class Id {

            value: string;

            constructor(id_json) {

                assert (id_json.length = 2);
                assert (id_json[0] === 'Id');

                this.value = id_json[1];
            }
        }
    }

    export class Pp {

    }

    namespace Goal {

        // type 'a hyp = (Names.Id.t list * 'a option * 'a)
        export type hyp<A> = [Array<Names.Id>, A | undefined, A];

        // type info =
        //     { evar : Evar.t
        //       ; name : Names.Id.t option
        //     }
        export interface info {

        }

        export interface reified_goal<A> {
            info: info;
            ty: A;
            hyp: hyp<A>;
        }
        export interface ser_goals<A> {
            goals: Array<A>;
            stack: Array<[Array<A>, Array<A>]>;
            bullet: Pp | undefined;
            shelf: Array<A>;
            given_up: Array<A>;
        }
    }

    export type LoadPath = Array<[Array<string>, Array<string>]>

    export type Options = Array<[string[], any]>

    export type TopMode = 'Interactive' | 'Vo'

}
