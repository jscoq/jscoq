//Provides: ml_z_mul_overflows
function ml_z_mul_overflows() {
    /* according to https://github.com/ocaml/Zarith/blob/39df015463f2797256dfb12440ed8f6c2dfd59cc/caml_z.c#L1469
     * it is always sound to return `true`, then `ml_z_mul` will handle it
     * in a general way. */
    return true;  
}