<template>
    <div class="entry">
        <span-editable ref="name" class="name" @input="rename">{{entry.name}}</span-editable>
        <file-list.tags :tags="entry.tags"/>
    </div>    
</template>

<script>
/**
 * `<file-list.file>`
 * Represents a file entry.
 */
export default {
    props: ['entry'],
    template: `
    `,
    methods: {
        renameStart() { this.$refs.name.edit(); },
        rename(v) {
            if (v != this.entry.name)
                this.$emit('action', {type: 'rename', from: this.entry.name, to: v});
        }
    },
    components: {
        'span-editable': require('./span-editable.vue').default,
        'file-list.tags': require('./tags.vue').default
    }
}
</script>