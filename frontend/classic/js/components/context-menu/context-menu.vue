<template>
    <vue-context-menu ref="m" @click.native="action" @ctx-close="onClose" @ctx-cancel="onClose" :class="theme">
        <slot></slot>
    </vue-context-menu>
</template>

<style src="./context-menu.css"></style>

<script>
import VueContextMenu from 'vue-context-menu'


export default {
    props: {theme: {default: 'compact'}},
    data: () => ({for: undefined}),
    components: {VueContextMenu},
    methods: {
        open(ev, whatFor) {
            this.for = whatFor;
            this.$refs.m.open(ev);
            this.$emit('open');
        },
        action(ev) {
            var item = ev.target.closest('*[name]');
            if (item) {
                var name = item.getAttribute('name');
                this.$emit('action', {type: name, for: this.for});
            }
        },
        onClose() {
            setTimeout(() => this.for = undefined, 0); /** @oops must happen after `action` handler */
            this.$emit('close');
        }
    }
}
</script>