<template>
    <span class="build-status">{{anim}}</span>    
</template>

<script>
export default {
    props: ['building'],
    data: () => ({anim: ''}),
    mounted() {
        this.$watch('building', flag => 
            flag ? this.setStatusAnimation() : this.clearStatusAnimation());
    },
    methods: {
        setStatusAnimation() {
            const l = [0,0,1,2,3].map(i => '∙'.repeat(i));
            var i = 2;
            this.anim = l[i];
            this._animInterval = setInterval(() => 
                this.anim = l[++i % l.length], 250);
        },
        clearStatusAnimation() {
            if (this._animInterval) clearInterval(this._animInterval);
            delete this._animInterval;
            this.anim = '';
        }
    }
}
</script>