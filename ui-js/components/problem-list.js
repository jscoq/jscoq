/**
 * A list of error messages with associated files and possibly location
 * information as well.
 */

const Vue = require('vue/dist/vue');



Vue.component('problem-list', {
    props: ['problems'],
    data: function() { return {
        pprint: undefined
    }; },
    template: `
    <ul class="problem-list">
        <li v-for="group in nonempty(problems)">
            {{noslash(group[0].entry.input)}}
            <ul class="problem-group">
                <li v-for="item in group"
                    v-html="msgHTML(item.error)">
                </li>
            </ul>
        </li>
    </ul>
    `,
    methods: {
        nonempty(l) {
            return l.filter(x => x.length);
        },
        noslash(s) {
            return s.replace(/^[/]/, '');
        },
        msgHTML(msg) {
            if (this.pprint) {
                return this.pprint.pp2HTML(msg);
            }
            else return msg;
        }
    }
});
