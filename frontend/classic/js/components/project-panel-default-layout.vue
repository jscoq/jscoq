<template>
    <div class="project-panel vertical-pane">
        <div class="toolbar">
            <project-context-menu ref="menu" :recent="recent"
                @action="$emit('menu:'+$event.type, $event)"/>
            <button @click="$emit('build')" :disabled="stopping">
                {{building ? 'stop' : 'build'}}</button>
            <project-build-status :building="building"/>
        </div>
        <file-list ref="file_list" :files="files" @action="fileAction"/>
        <project-file-context-menu ref="fileMenu"
            @action="fileMenuAction"/>
    </div>
</template>

<script>
import FileList from './file-list/index.vue';

export default {
    props: ['recent'],
    data: () => ({
        files: [], status: {}, building: false, compiled: false,
        stopping: false
    }),
    methods: {
        fileAction(action) {
            switch (action.type) {
            case 'menu':
                action.$event.preventDefault();
                this.$refs.fileMenu.open(action.$event, action);
                break;
            }
            this.$emit('action', action);
        },
        fileMenuAction(action) {
            const at = () => this._folderOf(action.for);
            switch (action.type) {
            case 'new-file':   this.create(at(), 'new-file#.v', 'file');    break;
            case 'new-folder': this.create(at(), 'new-folder#', 'folder');  break;
            case 'rename':     this.renameStart(action.for.path);           break;
            }
        },
        create(at, name, kind) {
            var newPath = this.$refs.file_list.freshName(at, name);
            this.$refs.file_list.create(newPath, kind);
            setTimeout(() => {
                this.$refs.file_list.renameStart(newPath);
            });
            this.$emit('action', {type: 'create', path: newPath, kind});
        },
        renameStart(path) {
            this.$refs.file_list.renameStart(path);
        },
        _folderOf(action) {
            return action.kind === 'folder' ? 
                       action.path : action.path.slice(0, -1);
        }
    },
    components: {FileList}
}
</script>