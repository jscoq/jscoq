<template>
    <span :contenteditable="editing" @click="click" @keydown="key" @blur="blur"><slot/></span>
</template>

<script>
export default {
    data: () => ({editing: false}),
    methods: {
        edit() {
            this._content = $(this.$el.childNodes).clone();
            this.editing = true;
            window.requestAnimationFrame(() => {
                selectElement(this.$el); this.$el.focus();
            });
        },
        accept() {
            var text = $(this.$el).text();
            if (text == '') this.abort();
            else {
                this.$emit('input', text);
                this.editing = false;
                this._content = null;
            }
        },
        abort() {
            this.editing = false;
            $(this.$el).html(this._content);
        },
        click(ev) {
            if (this.editing) ev.stopPropagation();
        },
        key(ev) {
            if (this.editing) {
                if (ev.key === 'Enter')        { this.accept(); ev.preventDefault(); }
                else if (ev.key === 'Escape')  { this.abort();  ev.preventDefault(); }
            }
        },
        blur(ev) {
            if (this.editing) { this.accept(); }
        }
    }
}

function selectElement(el) {
    var range = document.createRange();
    range.selectNodeContents(el);
    var sel = window.getSelection();
    sel.removeAllRanges();
    sel.addRange(range);
}
</script>