
/**
 * Allows to signal the worker that it is requested to interrupt its current
 * computation.
 * The page signals the worker by incrementing a 32-bit shared integer.
 * The worker periodically checks the integer, and would eventually break
 * its execution if the integer has been modified since the last time it was
 * read.
 */
class WorkerInterrupts {

    vec: Uint32Array
    checkpoint: number = 0

    setup(vec: Uint32Array) {
        this.vec = vec;
    }

    pending(): boolean {
        if (this.vec && typeof Atomics !== 'undefined') {
            var ld = Atomics.load(this.vec, 0);
            if (ld > this.checkpoint) {
                this.checkpoint = ld;
                return true;
            }
        }
        return false;
    }
}


export { WorkerInterrupts }