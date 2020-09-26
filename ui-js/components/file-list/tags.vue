<template>
    <div v-if="tags" class="tags">
        <span v-for="(t,$index) in tags" :key="$index"
              :class="t.class">{{displayText(t)}}</span>
    </div>
</template>

<script>
/**
 * `<file-list.tags>`
 * A small bin containing file tags.
 */
export default {
    props: ['tags'],
    methods: {
        displayText(t) {
            return t.text === undefined ? t : t.text;
        }
    }
}
</script>