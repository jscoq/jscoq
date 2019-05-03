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


Vue.component('file-list', {
    props: ['files', 'level', 'path'],
    data: function() { return {
        _level: this.level || 0,
        _path: typeof this.path === 'string' ? this.path.split('/') 
                : this.path || []
    }; },
    template: `
    <ul :class="['file-list', 'level-'+$data._level]">
        <li v-for="f in files" :data-name="f.name" :class="{folder: f.files, file: !f.files}"
                draggable="true" @dragstart="drag" @dragend="undrag" @drop="drop" @dragover="dragover" @dragleave="dragout">
            <folder v-if="f.files" :entry="f" :path="$data._path" :level="$data._level + 1"
                    @action="action"></folder>
            <span v-else class="name">{{f.name}}</span>
        </li>
    </ul>
    `,
    methods: {
        drag(ev) {
            var item_name = $(ev.currentTarget).attr('data-name'),
                from_path = [...this.$data._path, item_name];
            ev.dataTransfer.setData('text/json', JSON.stringify(from_path));
            $(event.currentTarget).addClass('dragged');
            ev.stopPropagation();
        },
        undrag(ev) {
            $(event.currentTarget).removeClass('dragged');
        },
        drop(ev) {
            var from_path = JSON.parse(ev.dataTransfer.getData('text/json')),
                item_name = $(ev.currentTarget).attr('data-name'),
                is_folder = $(ev.currentTarget).is('.folder'),
                to_path = this.$data._path.concat(is_folder ? item_name : []),
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
        dragover(ev) {
            if ($(ev.currentTarget).closest('.dragged').length === 0) {
                $(ev.currentTarget).addClass('draghov');
                ev.preventDefault();
            }
            ev.stopPropagation();
        },
        dragout(ev) {
            $(ev.currentTarget).removeClass('draghov');
        },

        action(ev) {
            if (this.$data._level === 0) {
                switch (ev.type) {
                    case 'move': this.move(ev.from, ev.to, ev.after); break;
                }
            }
            else
                this.$emit('action', ev);
        },

        move(from, to, after) {
            let src = this.lookup(from.slice(0,-1)), src_name = from[from.length - 1],
                dest = this.lookup(to);
            if (src && src.files && dest) {
                var src_index = src.files.findIndex(e => e.name === src_name),
                    dest_index = after ? dest.files.findIndex(e => e.name === after) : -1;
                if (src_index > -1) {
                    var e = src.files[src_index];
                    src.files.splice(src_index, 1);
                    dest.files.splice(dest_index + 1, 0, e);
                }
            }
        },

        lookup(rel_path) {
            if (typeof rel_path === 'string') rel_path = rel_path.split('/');

            var cwd = {name: '/', files: this.files};
            for (let pel of rel_path) {
                if (!cwd || !cwd.files) return;
                cwd = cwd.files.find(e => e.name === pel);
            }
            return cwd;
        },

        create(rel_path, type='file') {
            if (typeof rel_path === 'string') rel_path = rel_path.split('/');

            var cwd = {name: '/', files: this.files};
            for (let pel of rel_path) {
                if (!cwd.files) cwd.files = [];
                let e = cwd.files.find(e => e.name === pel);
                if (!e) {
                    e = {name: pel, files: undefined};
                    cwd.files.push(e);
                }
                cwd = e;
            }
            if (type === 'folder' && !cwd.files)
                cwd.files = [];
            return cwd;
        }
    }
});

/**
 * `<folder>`
 * Represents a subfolder.
 */
Vue.component('folder', {
    props: ['entry', 'level', 'path', 'collapsed'],
    data: function() { return {
        _path: [...(this.path || []), this.entry.name],
        _collapsed: !!this.collapsed
    }; },
    template: `
    <div :class="['level-'+level]">
        <div class="name">
            <folder-knob v-model="$data._collapsed"></folder-knob>
            {{entry.name}}
        </div>
        <file-list :files="entry.files" :path="$data._path" :level="level"
                   v-show="!$data._collapsed"
                   @action="$emit('action', $event)">
        </file-list>
    </div>
    `
})

/**
 * `<folder-knob>`
 * A small widget for expanding/collapsing a subfolder.
 */
Vue.component('folder-knob', {
    props: ['value'],
    data: function() { return {checked: !!this.value}; },
    template: `
    <span class="folder-knob" :class="{checked: checked}"
        @click="$emit('input', (checked = !checked))"></span>
    `
});

