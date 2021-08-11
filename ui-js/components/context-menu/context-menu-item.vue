<template>
    <li :name="name" :class="{disabled: !enabled}"><slot></slot></li>
</template>

<script>
export default {
    props: {'name': {}, 'enabled': {default: true}}
}
</script>