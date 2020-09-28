<template>
    <span class="folder-knob" :class="{checked}"
        @click="$emit('input', !checked)"></span>
</template>

<script>
/**
 * `<file-list.folder-knob>`
 * A small widget for expanding/collapsing a subfolder.
 */
export default {
    props: ['value'],
    computed: { checked() { return !!this.value} }
}
</script>