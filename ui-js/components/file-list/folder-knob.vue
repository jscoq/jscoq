<template>
    <span class="folder-knob" :class="{checked: checked}"
        @click="$emit('input', (checked = !checked))"></span>
</template>

<script>
/**
 * `<file-list.folder-knob>`
 * A small widget for expanding/collapsing a subfolder.
 */
export default {
    props: ['value'],
    data: function() { return {checked: !!this.value}; }
}
</script>