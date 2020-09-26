<template>
    <vue-context ref="m">
        <li><a name="new-file" @click="action">New file</a></li>
        <li><a name="new-folder" @click="action">New foler</a></li>
        <li><a name="rename" @click="action">Rename</a></li>
    </vue-context>
</template>

<script>
import VueContext from 'vue-context';

function vueContextCleanup() {
    if ($('.v-context').is(':visible')) $(document.body).click();
}

export default {
    components: {VueContext},
    methods: {
        open(ev, action) {
            vueContextCleanup();
            this._for = action;
            this.$refs.m.open(ev); 
        },
        action(ev) {
            if (!$(ev.currentTarget).is('[disabled]'))
                this.$emit('action', {type: ev.currentTarget.name, for: this._for});
        }
    }    
}
</script>