<template>
    <context-menu ref="m" @action="$emit('action', $event)">
        <item name="new-file">New file</item>
        <item name="new-folder">New folder</item>
        <item name="rename">Rename</item>
    </context-menu>
</template>

<script>
//import VueContext from 'vue-context';
import ContextMenu from './context-menu/context-menu.vue';
import ContextMenuItem from './context-menu/context-menu-item.vue';

function vueContextMenuCleanup() {
    if ($('.ctx-menu-container').is(':visible')) $(document.body).click();
}

export default {
    components: { ContextMenu, item: ContextMenuItem },
    methods: {
        open(ev, action) {
            vueContextMenuCleanup();
            this.$refs.m.open(ev, action); 
        }
    }    
}
</script>