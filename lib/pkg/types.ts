// .coq-pkg files
export namespace Package {
    // coq-pkg.json manifest
    export interface Manifest {
        name: string;
        deps: string[];
        modules: { [module: string]: { deps?: string[] } };
    }
}

export namespace Bundle {
    // $pkg.json manifest
    export interface Manifest {
        name: string;
        deps: string[];
        pkgs: string[];
        chunks: Package.Manifest[];
    }
}