<template>
    <span class="project-context-menu" :class="{open: isOpen}">
        <button @click.stop.prevent="toggle"><hamburger-svg/></button>
        <context-menu ref="m" @open="isOpen = true" @close="isOpen = false"
                @action="$emit('action', $event)">
            <item name="new" :enabled="!$root.building">New Project</item>
            <item name="open" :enabled="!$root.building">Open Project...</item>
            <!-- @todo submenus currently not supported in vue-context-menu
            <li class="v-context__sub" v-if="recent"><a>Open Recent</a>
                <ul>
                    <item v-for="entry in recent" :key="entry.uri" 
                        name="open-recent">{{entry.uri}}</item>
                </ul>
            </li> -->
            <item name="download-v">Download sources</item>
            <item name="download-vo" :enabled="!$root.building && $root.compiled">Download compiled</item>
        </context-menu>
    </span>
</template>

<script>
import ContextMenu from './context-menu/context-menu.vue';
import ContextMenuItem from './context-menu/context-menu-item.vue';
import HamburgerSvg from './hamburger-svg.vue';

function vueContextMenuCleanup() {
    if ($('.ctx-menu-container').is(':visible')) $(document.body).click();
}

export default {
    props: ['recent'],
    data: () => ({isOpen: false}),
    components: {ContextMenu, item: ContextMenuItem, HamburgerSvg},
    methods: {
        toggle() {
            console.log(this.$refs.m.show)
            if (this.$refs.m.show) this.$refs.m.close();
            else {
                vueContextMenuCleanup();
                this.$refs.m.open({clientX: this.$parent.$el.clientWidth, clientY: 0}); 
            }
        }
    }   
}
</script>