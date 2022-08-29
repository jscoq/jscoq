<template>
    <ul :class="['file-list', 'level-'+$data._level]" @drop="drop"
            @dragover="dragover" @dragenter="dragover" @dragleave="dragout"
            @contextmenu.stop="menu">
        <li v-for="f in files" :data-name="f.name" :key="f.name"
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
</template>

<script>
import _ from 'lodash';

export default {
    name: 'file-list',
    props: ['files', 'level', 'path', 'selection_'],
    data: function() { return {
        _level: this.level || 0,  // assume level does not change :/
        _selection: []
    }; },
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
            //if ($('.ctx-menu-container').is(':visible'))
            //    $(document.body).click();
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
            $(ev.currentTarget).removeClass('dragged');
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

        select(path, expose = true) {
            path = promotePath(path);
            if (expose) this.expose(path);
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

        lookup(path) {
            path = promotePath(path);

            var cwd = {name: '/', files: this.files};
            for (let pel of path) {
                if (!cwd || !cwd.files) return;
                cwd = cwd.files.find(e => e.name === pel);
            }
            return cwd;
        },
        lookupComponent(path) {
            path = promotePath(path);

            var cur = this;
            for (let pel of path) {
                if (cur.$refs.l) cur = cur.$refs.l;
                cur = (cur.$refs.entries || []).find(e => e.entry.name === pel);
                if (!cur) return;
            }
            return cur;
        },

        create(path, kind='file') {
            path = promotePath(path);

            var cwd = {name: '/', files: this.files};
            for (let pel of path) {
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

        freshName(path, template='u#') { 
            path = promotePath(path);
            var e = this.lookup(path), name = template.replace('#', '');
            if (e) {
                var i = 0;
                for (;;) {
                    if (!e.files.find(f => f.name === name)) break;
                    name = template.replace('#', `-${++i}`);
                }
            }
            return [...path, name];
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
        expandAll(max_depth = 10) {
            if (max_depth <= 0) return;
            for (let e of this.$refs.entries || []) {
                if (e.$data.hasOwnProperty('_collapsed'))
                    e.$data._collapsed = false;
            }
        },

        expose(path) {
            path = promotePath(path);

            for (let idx = 1; idx < path.length; idx++) {
                var e = this.lookupComponent(path.slice(0, idx));
                if (e && e.$data.hasOwnProperty('_collapsed'))
                    e.$data._collapsed = false;
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
    },
    components: {
        'file-list.file': require('./file.vue').default,
        'file-list.folder': require('./folder.vue').default
    }
}

function promotePath(path) {
    return typeof path === 'string' ? path.split('/').filter(x => x) : path;
}
</script>