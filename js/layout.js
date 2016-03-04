"use strict";

class GridLayout {

    constructor(selector) {
        var options = {
            cell_height: Math.floor((document.documentElement.clientHeight - 83) / 14),
            resizable: {
                handles: 'e, se, s, sw, w'
            },
            vertical_margin: 2,
            handle: '.jscoq-panel-wrapper .caption',
        };
        $(selector).gridstack(options);
        $(selector).on('change', (evt, items) => this.save(evt, items));
        this.grid = $(selector).data('gridstack');

        var saved_layout = GridLayout.getCookie('jscoq_grid_state');
        if(saved_layout) {
            this.load(JSON.parse(saved_layout));
        }
        this.skip_save_events = false;

        this.presets = {
            Default: {
                "proof": {"x":8,"y":0,"width":4,"height":6},
                "query":{"x":8,"y":6,"width":4,"height":5},
                "packages":{"x":8,"y":11,"width":4,"height":3},
                "document":{"x":0,"y":0,"width":8,"height":14}},
            Projector: {
                "document":{"x":0,"y":0,"width":12,"height":9},
                "query":{"x":8,"y":9,"width":4,"height":5},
                "proof":{"x":0,"y":9,"width":8,"height":5},
                "packages":{"x":0,"y":14,"width":12,"height":1}},
        };
    }

    save(evt, items) {
        if (this.skip_save_events)
            return;

        var state = {};
        items.map((item) =>
            {
                var name = item.el[0].getAttribute('data-jscoq-name');
                state[name] = {x: item.x,
                              y: item.y,
                              width: item.width,
                              height: item.height};
            }
        )
        document.cookie = 'jscoq_grid_state=' + JSON.stringify(state);
        console.info('layout saved');
    }

    loadPreset(name) {
        var layout = this.presets[name];
        if (!layout) return;
        this.load(layout);
    }

    load(layout) {
        this.skip_save_events = true;
        var engine = this.grid.grid;
        engine.nodes.forEach(
            item => {
                var name = item.el[0].getAttribute('data-jscoq-name');
                this.grid.resize(item.el, 1, 1);
                this.grid.move(item.el, layout[name].x, layout[name].y);
                this.grid.resize(item.el, layout[name].width, layout[name].height);
            }
        )
        this.skip_save_events = false;
        this.save(null, engine.nodes);
    }

    static getCookie(name) {
        // from w3schools.com
        var nameEQ = name + "=";
        var ca = document.cookie.split(';');
        var i;
        for(i=0 ; i < ca.length ; i++) {
            var c = ca[i];
            while (c.charAt(0)==' '){c = c.substring(1);}
            if (c.indexOf(nameEQ) != -1){return c.substring(nameEQ.length,c.length);}
        }
        return null;
    }
}
