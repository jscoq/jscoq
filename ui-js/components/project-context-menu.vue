<template>
    <span class="project-context-menu" :class="{open: isOpen}">
        <button @click.stop.prevent="open"><hamburger-svg/></button>
        <vue-context ref="m" @open="isOpen = true" @close="isOpen = false">
            <li><a name="new" @click="action" :disabled="$root.building">New Project</a></li>
            <li><a name="open" @click="action" :disabled="$root.building">Open Project...</a></li>
            <li><a name="download-v" @click="action">Download sources</a></li>
            <li><a name="download-vo" @click="action" :disabled="$root.building || !$root.compiled">Download compiled</a></li>
        </vue-context>
    </span>
</template>

<script>
import VueContext from 'vue-context';
import HamburgerSvg from './hamburger-svg.vue';

function vueContextCleanup() {
    if ($('.v-context').is(':visible')) $(document.body).click();
}

export default {
    data: () => ({isOpen: false}),
    components: {VueContext, HamburgerSvg},
    methods: {
        open() {
            if (this.$refs.m.show) this.$refs.m.close();
            else {
                vueContextCleanup();
                this.$refs.m.open({clientX: this.$parent.$el.clientWidth, clientY: 0}); 
            }
        },
        action(ev) {
            if (!$(ev.currentTarget).is('[disabled]'))
                this.$emit('action', {type: ev.currentTarget.name});
        }
    }   
}
</script>