/**
 * A collapsible directory structure view (based on Vue).
 * 
 * The data is organized as a tree, where every element is of the form
 * {name: "...", files: [ ... ]}.
 * For leaf nodes (files), the `files` property will be undefined.
 * For internal nodes (folders), `files` will be a list of sub-trees with
 * the same format.
 * 
 * The main component is `<file-list>`, and it uses `<folder>` and
 * `<folder-knob>` internally.
 */

import Vue from 'vue/dist/vue';
import _ from 'lodash';



Vue.component('file-list', {
    props: ['files', 'level', 'path', 'selection_'],
    data: function() { return {
        _level: this.level || 0,  // assume level does not change :/
        _selection: []
    }; },
    template: `
    <ul :class="['file-list', 'level-'+$data._level]" @drop="drop"
            @dragover="dragover" @dragenter="dragover" @dragleave="dragout"
            @contextmenu.stop="menu">
        <li v-for="f in files" :data-name="f.name" 
                :class="{folder: f.files, file: !f.files, selected: isSelected([f.name])}"
                @click.stop="onclick" @mouseup.stop="onrightclick"
                draggable="true" @dragstart="drag" @dragend="undrag" @drop="drop" 
                @dragover="dragover" @dragenter="dragover" @dragleave="dragout"
                @contextmenu.stop="menu">
            <file-list.folder v-if="f.files" ref="entries" :entry="f" :path="_path" :level="$data._level + 1"
                    :selection="$data._selection" @action="action"/>
            <file-list.file v-else ref="entries" :entry="f" @action="action"/>
        </li>
    </ul>
    `,
    computed: {
        _path() { return typeof this.path === 'string' ? this.path.split('/') 
                                                       : this.path || []; },
        selection() { return this.selection_ || this.$data._selection || []; }
    },
    methods: {
        onclick(ev) {
            var target = $(ev.currentTarget),
                item_name = target.attr('data-name'),
                path = [...this._path, item_name],
                kind = target.hasClass('folder') ? 'folder' : 'file';
            this.action({type: 'select', path, kind});
            if ($('.v-context').is(':visible'))
                $(document.body).click();
        },
        onrightclick(ev) {
            if (ev.which === 3 || ev.button === 2)   /* Right click... :\ */
                this.onclick(ev);
        },
        drag(ev) {
            var target = $(ev.currentTarget),
                item_name = target.attr('data-name'),
                from_path = [...this._path, item_name];
            ev.dataTransfer.setData('text/json', JSON.stringify(from_path));
            requestAnimationFrame(() => target.addClass('dragged'));
            ev.stopPropagation();
        },
        undrag(ev) {
            $(event.currentTarget).removeClass('dragged');
        },
        drop(ev) {
            $(ev.currentTarget).removeClass('draghov');

            if (ev.dataTransfer.files.length) return this.dropFiles(ev);

            var evdata = ev.dataTransfer.getData('text/json');
            if (!evdata) return;

            var from_path = JSON.parse(evdata),
                target = $(ev.currentTarget),
                item_name = target.attr('data-name'),
                is_folder = target.is('.folder'),
                to_path = this._path.concat(is_folder ? item_name : []),
                after_name = is_folder ? null : item_name;
            this.action({
                type: 'move',
                from: from_path,
                to: to_path, 
                after: after_name
            });
            $(ev.currentTarget).removeClass('draghov');
            ev.stopPropagation();
        },
        dropFiles(ev) {
            var dt = ev.dataTransfer;
            console.log([...dt.files]);
            for (let fl of [...dt.files]) {
                this.action({type: 'create', path: [fl.name], kind: 'file', content: fl});
            }
            ev.stopPropagation();
            ev.preventDefault();
        },
        dragover(ev) {
            if ($(ev.currentTarget).closest('.dragged').length === 0) {
                $(ev.currentTarget).addClass('draghov');
                ev.preventDefault();
                ev.dataTransfer.dropEffect = 'move';
            }
            ev.stopPropagation();
        },
        dragout(ev) {
            $(ev.currentTarget).removeClass('draghov');
        },

        menu(ev) {
            var target = $(ev.currentTarget),
                item_name = target.attr('data-name'), path, kind;
            if (item_name) {
                path = [...this._path, item_name],
                kind = target.hasClass('folder') ? 'folder' : 'file';
            }
            else {
                path = this._path; kind = 'folder';
            }
            this.action({type: 'menu', path, kind, $event: ev});
        },

        action(ev) {
            if (!ev.path) ev.path = this._path;
            if (this.$data._level === 0) {
                switch (ev.type) {
                    case 'select': 
                        if (ev.kind === 'file') this.select(ev.path); break;
                    case 'move': this.move(ev.from, ev.to, ev.after); break;
                    case 'rename': this.rename(ev.path, ev.from, ev.to); break;
                }
            }
            this.$emit('action', ev);
        },

        select(path) {
            this.$data._selection = [path];
        },
        isSelected(path) {
            return this.selection.some(x => _.isEqual(x, path));
        },

        move(from, to, after) {
            let src = this.lookup(from.slice(0,-1)), [src_name] = from.slice(-1),
                dest = this.lookup(to);
            if (src && src.files && dest) {
                var src_index = src.files.findIndex(e => e.name === src_name),
                    dest_index = after ? dest.files.findIndex(e => e.name === after) + 1 : 0;
                if (src_index > -1) {
                    var e = src.files[src_index];
                    if (src.files === dest.files && src_index < dest_index)
                        dest_index--;
                    src.files.splice(src_index, 1);
                    dest.files.splice(dest_index, 0, e);
                }
            }
        },

        lookup(rel_path) {
            if (typeof rel_path === 'string') rel_path = rel_path.split('/').filter(x => x);

            var cwd = {name: '/', files: this.files};
            for (let pel of rel_path) {
                if (!cwd || !cwd.files) return;
                cwd = cwd.files.find(e => e.name === pel);
            }
            return cwd;
        },
        lookupComponent(rel_path) {
            if (typeof rel_path === 'string') rel_path = rel_path.split('/').filter(x => x);

            var cur = this;
            for (let pel of rel_path) {
                if (cur.$refs.l) cur = cur.$refs.l;
                cur = (cur.$refs.entries || []).find(e => e.entry.name === pel);
                if (!cur) return;
            }
            return cur;
        },

        create(rel_path, kind='file') {
            if (typeof rel_path === 'string')
                rel_path = rel_path.split('/').filter(x => x);

            var cwd = {name: '/', files: this.files};
            for (let pel of rel_path) {
                if (!cwd.files) cwd.files = [];
                let e = cwd.files.find(e => e.name === pel);
                if (!e) {
                    e = {name: pel, files: undefined, tags: undefined};
                    cwd.files.push(e);
                }
                cwd = e;
            }
            if (kind === 'folder' && !cwd.files)
                cwd.files = [];
            return cwd;
        },

        freshName(rel_path, template='u#') { 
            var e = this.lookup(rel_path), name = template.replace('#', '');
            if (e) {
                var i = 0;
                for (;;) {
                    if (!e.files.find(f => f.name === name)) break;
                    name = template.replace('#', `-${++i}`);
                }
            }
            return [...rel_path, name];
        },

        renameStart(rel_path) {
            var c = this.lookupComponent(rel_path);
            if (c && c !== this) c.renameStart();
        },
        rename(rel_path, from, to) {
            var e = this.lookup([...rel_path, from]);
            e.name = to;
        },

        collapseAll() {
            for (let e of this.$refs.entries || []) {
                if (e.$data.hasOwnProperty('_collapsed'))
                    e.$data._collapsed = true;
            }
        },

        *iter(cwd, prefix=[]) {
            cwd = cwd || {name: '/', files: this.files};

            for (let fl of cwd.files || []) {
                var fn = [...prefix, fl.name];
                yield {path: fn, kind: fl.files ? 'folder' : 'file', entry: fl};
                if (fl.files) yield* this.iter(fl, fn);
            }
        },

        clear() {
            this.files.splice(0);
        },

        populate(files, clearFirst = true) {
            if (clearFirst) this.clear();
            for (let fn of files) this.create(fn);
        }
    }
});

/**
 * `<file-list.file>`
 * Represents a file entry.
 */
Vue.component('file-list.file', {
    props: ['entry'],
    template: `
    <div class="entry">
        <span-editable ref="name" class="name" @input="rename">{{entry.name}}</span-editable>
        <file-list.tags :tags="entry.tags"/>
    </div>
    `,
    methods: {
        renameStart() { this.$refs.name.edit(); },
        rename(v) {
            if (v != this.entry.name)
                this.$emit('action', {type: 'rename', from: this.entry.name, to: v});
        }
    }
});


/**
 * `<file-list.folder>`
 * Represents a subfolder.
 */
Vue.component('file-list.folder', {
    props: ['entry', 'level', 'path', 'selection', 'collapsed'],
    data: function() { return {
        _collapsed: !!this.collapsed
    }; },
    template: `
    <div :class="['level-'+level]">
        <div class="entry">
            <file-list.folder-knob v-model="$data._collapsed"/>
            <span-editable ref="name" class="name">{{entry.name}}</span-editable>
        </div>
        <file-list ref="l" :files="entry.files" :path="_path" :level="level"
                   :selection_="subselection(selection, entry.name)"
                   v-show="!$data._collapsed"
                   @action="$emit('action', $event)">
        </file-list>
    </div>
    `,
    computed: {
        _path() { return [...(this.path || []), this.entry.name]; }
    },
    methods: {
        subselection(selection, folder_name) {
            if (selection) {
                return selection.filter(x => x[0] === folder_name)
                                .map(x => x.slice(1));
            }
        },
        renameStart() { this.$refs.name.edit(); },
        rename(v) {
            if (v != this.entry.name)
                this.$emit('action', {type: 'rename', from: this.entry.name, to: v});
        }
    }
})

/**
 * `<file-list.folder-knob>`
 * A small widget for expanding/collapsing a subfolder.
 */
Vue.component('file-list.folder-knob', {
    props: ['value'],
    data: function() { return {checked: !!this.value}; },
    template: `
    <span class="folder-knob" :class="{checked: checked}"
        @click="$emit('input', (checked = !checked))"></span>
    `
});

/**
 * `<file-list.tags>`
 * A small bin containing file tags.
 */
Vue.component('file-list.tags', {
    props: ['tags'],
    template: `
    <div v-if="tags" class="tags">
        <span v-for="t in tags" :class="t.class">{{displayText(t)}}</span>
    </div>
    `,
    methods: {
        displayText(t) {
            return t.text === undefined ? t : t.text;
        }
    }
});


Vue.component('span-editable', {
    data: () => ({editing: false}),
    template: `<span :contenteditable="editing" @click="click" @keydown="key" @blur="blur"><slot/></span>`,
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
});

function selectElement(el) {
    var range = document.createRange();
    range.selectNodeContents(el);
    var sel = window.getSelection();
    sel.removeAllRanges();
    sel.addRange(range);
}

