"use strict";

class PackageManager {

    constructor(panel, base_path, coq) {
        this.base_path = base_path;
        this.panel   = panel;
        this.bundles = {};
        this.coq     = coq;
    }

    addBundleInfo(bname, pkg_info) {

        var div  = document.createElement('div');
        var dsel = d3.select(div);

        dsel.data([pkg_info]);

        dsel.append('img')
            .attr('src', this.base_path + 'ui-images/dl.png')
            .on('click', () => { this.startPackageDownload(); });

        dsel.append('span')
            .text(d => d.desc);

        this.panel.appendChild(div);

        var desc = pkg_info.desc;
        var pkgs = pkg_info.pkgs;
        var no_files = 0;

        for(var i = 0; i < pkgs.length; i++)
            // pkgs[i].cma_files.length XXX
            no_files += pkgs[i].vo_files.length;

        pkg_info.loaded = 0;
        pkg_info.total  = no_files;

        this.bundles[bname] = { div: div, info: pkg_info };

    }

    // XXX [EG]: This needs to be tweaked, package loading could be
    // externally initiated.
    startPackageDownload() {

        var row = d3.select(d3.event.target.parentNode);

        let bp = this.base_path + "../coq-pkgs/";
        this.coq.sendCommand(["LoadPkg", bp, row.datum().desc]);

    }

    // In all the three cases below, evt = progressInfo
    // bundle : string
    // pkg    : string
    // loaded : int
    // total  : int

    onBundleStart(bname) {

        var div  = this.bundles[bname].div;
        // var row  = d3.select(this.panel).selectAll('div')
        //     .filter(pkg => pkg.desc === evt.bundle_name);

        // XXX: Workaround, in case this is called multiple times, add
        // the bar only the first time. We could be smarter.

        if (! this.bundles[bname].bar ) {

            var row  = d3.select(div);

            var bar = row.append('div')
                .attr('class', 'rel-pos')
                .append('div')
                .attr('class', 'progressbar');

            var egg = bar
                .append('img')
                .attr('src', this.base_path + 'ui-images/egg.png')
                .attr('class', 'progress-egg');

            this.bundles[bname].bar = bar;
            this.bundles[bname].egg = egg;
        }
    }


    onPkgProgress(evt) {

        // We get rid of the start notification.
        if(!this.bundles[evt.bundle].bar)
            this.onBundleStart(evt.bundle);

        var info = this.bundles[evt.bundle].info;
        var bar  = this.bundles[evt.bundle].bar;
        var egg  = this.bundles[evt.bundle].egg;

        var progress = ++info.loaded / info.total;
        var angle    = (progress * 360 * 15) % 360;
        egg.style('transform', 'rotate(' + angle + 'deg)');
        bar.style('width', progress * 100 + '%');
    }

    onBundleLoad(bundle) {

        var info = this.bundles[bundle].info;
        var div  = this.bundles[bundle].div;
        var row  = d3.select(div);

        row.select('.rel-pos').remove();
            row.select('img')
                .attr('src', this.base_path + 'ui-images/checked.png');
    }
}

// EG: This will be useful once we move file downloading to javascript.
// PackagesManager

class PackageDowloader {

    constructor(row, panel) {
        this.row = row;
        this.bar = null;
        this.egg = null;
        this.bundle_name = row.datum().desc;
        this.panel = panel;
        this.progress = 0; // percent
    }

    // This method setups the download handling.
    download() {

        // Allow re-download
        // this.row.select('img').on('click', null);

        this.bar = this.row.append('div')
            .attr('class', 'rel-pos')
            .append('div')
            .attr('class', 'progressbar');

        this.egg = this.bar
            .append('img')
            .attr('src', 'ui-images/egg.png')
            .attr('class', 'progress-egg');

        var files_total_length = 0;
        var files_loaded_cpt = 0;
        var pkgs = this.row.datum().pkgs;

        // Proceed to the main download.
        for(var i = 0; i < pkgs.length; i++)
            files_total_length += pkgs[i].no_files;

        document.body.addEventListener('pkgProgress',
            (evt) => {
                if(evt.detail.bundle_name === this.bundle_name) {
                    this.progress = ++files_loaded_cpt / files_total_length;
                    this.updateProgress();
                    if (files_loaded_cpt === files_total_length)
                        this.finishDownload();
                }
            }
        );

        jsCoq.add_pkg(this.bundle_name);

    }

    updateProgress() {
        var angle = (this.progress * 360 * 15) % 360;
        this.egg.style('transform', 'rotate(' + angle + 'deg)');
        this.bar.style('width', this.progress * 100 + '%');
    }

    finishDownload() {
        this.row.select('.rel-pos').remove();
        this.row.select('img')
            .attr('src', 'ui-images/checked.png');
    }
}

// Local Variables:
// js-indent-level: 4
// End:
